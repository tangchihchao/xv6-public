// File system implementation.  Five layers:
//   + Blocks: allocator for raw disk blocks.
//   + Log: crash recovery for multi-step updates.
//   + Files: inode allocator, reading, writing, metadata.
//   + Directories: inode with special contents (list of other inodes!)
//   + Names: paths like /usr/rtm/xv6/fs.c for convenient naming.
//
// This file contains the low-level file system manipulation
// routines.  The (higher-level) system call implementations
// are in sysfile.c.

#include "types.h"
#include "defs.h"
#include "param.h"
#include "stat.h"
#include "mmu.h"
#include "proc.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "buf.h"
#include "file.h"

#define min(a, b) ((a) < (b) ? (a) : (b))
static void itrunc(struct inode*);
// there should be one superblock per disk device, but we run with
// only one device
struct superblock sb; 

// Read the super block.
void
readsb(int dev, struct superblock *sb)
{
  struct buf *bp;

  bp = bread(dev, 1);
  memmove(sb, bp->data, sizeof(*sb));
  brelse(bp);
}

// Zero a block.
static void
bzero(int dev, int bno)
{
  struct buf *bp;

  bp = bread(dev, bno);
  memset(bp->data, 0, BSIZE);
  log_write(bp);
  brelse(bp);
}

// Blocks.

// Allocate a zeroed disk block.
static uint
balloc(uint dev)
{
  int b, bi, m;
  struct buf *bp;

  bp = 0;
  for(b = 0; b < sb.size; b += BPB){
    bp = bread(dev, BBLOCK(b, sb));
    for(bi = 0; bi < BPB && b + bi < sb.size; bi++){
      m = 1 << (bi % 8);
      if((bp->data[bi/8] & m) == 0){  // Is block free?
        bp->data[bi/8] |= m;  // Mark block in use.
        log_write(bp);
        brelse(bp);
        bzero(dev, b + bi);
        return b + bi;
      }
    }
    brelse(bp);
  }
  panic("balloc: out of blocks");
}

// Free a disk block.
static void
bfree(int dev, uint b)
{
  struct buf *bp;
  int bi, m;

  readsb(dev, &sb);
  bp = bread(dev, BBLOCK(b, sb));
  bi = b % BPB;
  m = 1 << (bi % 8);
  if((bp->data[bi/8] & m) == 0)
    panic("freeing free block");
  bp->data[bi/8] &= ~m;
  log_write(bp);
  brelse(bp);
}

// Inodes.
//
// An inode describes a single unnamed file.
// The inode disk structure holds metadata: the file's type,
// its size, the number of links referring to it, and the
// list of blocks holding the file's content.
//
// The inodes are laid out sequentially on disk at
// sb.startinode. Each inode has a number, indicating its
// position on the disk.
//
// The kernel keeps a cache of in-use inodes in memory
// to provide a place for synchronizing access
// to inodes used by multiple processes. The cached
// inodes include book-keeping information that is
// not stored on disk: ip->ref and ip->valid.
//
// An inode and its in-memory representation go through a
// sequence of states before they can be used by the
// rest of the file system code.
//
// * Allocation: an inode is allocated if its type (on disk)
//   is non-zero. ialloc() allocates, and iput() frees if
//   the reference and link counts have fallen to zero.
//
// * Referencing in cache: an entry in the inode cache
//   is free if ip->ref is zero. Otherwise ip->ref tracks
//   the number of in-memory pointers to the entry (open
//   files and current directories). iget() finds or
//   creates a cache entry and increments its ref; iput()
//   decrements ref.
//
// * Valid: the information (type, size, &c) in an inode
//   cache entry is only correct when ip->valid is 1.
//   ilock() reads the inode from
//   the disk and sets ip->valid, while iput() clears
//   ip->valid if ip->ref has fallen to zero.
//
// * Locked: file system code may only examine and modify
//   the information in an inode and its content if it
//   has first locked the inode.
//
// Thus a typical sequence is:
//   ip = iget(dev, inum)
//   ilock(ip)
//   ... examine and modify ip->xxx ...
//   iunlock(ip)
//   iput(ip)
//
// ilock() is separate from iget() so that system calls can
// get a long-term reference to an inode (as for an open file)
// and only lock it for short periods (e.g., in read()).
// The separation also helps avoid deadlock and races during
// pathname lookup. iget() increments ip->ref so that the inode
// stays cached and pointers to it remain valid.
//
// Many internal file system functions expect the caller to
// have locked the inodes involved; this lets callers create
// multi-step atomic operations.
//
// The icache.lock spin-lock protects the allocation of icache
// entries. Since ip->ref indicates whether an entry is free,
// and ip->dev and ip->inum indicate which i-node an entry
// holds, one must hold icache.lock while using any of those fields.
//
// An ip->lock sleep-lock protects all ip-> fields other than ref,
// dev, and inum.  One must hold ip->lock in order to
// read or write that inode's ip->valid, ip->size, ip->type, &c.

struct {
  struct spinlock lock;
  struct inode inode[NINODE];
} icache;

void
iinit(int dev)
{
  int i = 0;
  
  initlock(&icache.lock, "icache");
  for(i = 0; i < NINODE; i++) {
    initsleeplock(&icache.inode[i].lock, "inode");
  }

  readsb(dev, &sb);
  cprintf("sb: size %d nblocks %d ninodes %d nlog %d logstart %d\
 inodestart %d bmap start %d\n", sb.size, sb.nblocks,
          sb.ninodes, sb.nlog, sb.logstart, sb.inodestart,
          sb.bmapstart);
}

struct inode* iget(uint dev, uint inum);

//PAGEBREAK!
// Allocate an inode on device dev.
// Mark it as allocated by  giving it type type.
// Returns an unlocked but allocated and referenced inode.
struct inode*
ialloc(uint dev, short type)
{
  int inum;
  struct buf *bp;
  struct dinode *dip;

  for(inum = 1; inum < sb.ninodes; inum++){
    bp = bread(dev, IBLOCK(inum, sb));
    dip = (struct dinode*)bp->data + inum%IPB;
    if(dip->type == 0){  // a free inode
      memset(dip, 0, sizeof(*dip));
      dip->type = type;
      log_write(bp);   // mark it allocated on the disk
      brelse(bp);
      return iget(dev, inum);
    }
    brelse(bp);
  }
  panic("ialloc: no inodes");
}

//Compute inode checksum
uint ichecksum(struct inode *ip)
{

  // We do not want to checksum files like console
  if (ip->type == T_DEV) // 註1
    return 0;

  unsigned int buf[512];
  char *cbuf = (char *)buf; // sets cbuf to point to buf's pointee
  uint n = sizeof(buf);
  uint off = 0;
  uint r, i;
  unsigned int checksum = 0;
  memset((void *)cbuf, 0, n); // 將cbuf全部值設為0
  unsigned int *bp;

  // readi不停將inode *ip值寫入cbuf中(一次大小為n)
  // for迴圈一次跑完 [sizeof(buf) / sizeof(uint)] == n
  //     一一取出buf中的值，一一讓checksum ^= *bp (XOR運算)
  //     bp指針隨for迴圈持續前進，直到迴圈跳出
  while ((r = readi(ip, cbuf, off, n)) > 0)
  {                           // 將ip中的資料依序讀入cbuf中(註2)
    off += r;                 // r == n
    bp = (unsigned int *)buf; // sets bp to point to buf's pointee

    // 讀取存在buf中的每個unsigned int
    for (i = 0; i < sizeof(buf) / sizeof(uint); i++)
    {

      // buf == char* cbuf
      // *bp == (unsigned int *)buf
      checksum ^= *bp;
      bp++;
    }
    memset((void *)cbuf, 0, n); // 將cbuf全部值重設為0
  }

  return checksum;
}

// Copy a modified in-memory inode to disk.
// Must be called after every change to an ip->xxx field
// that lives on disk, since i-node cache is write-through.
// Caller must hold ip->lock.
void
iupdate(struct inode *ip)
{
  iupdate_ext(ip, 0);
}

// Update a child-inode
void cupdate(struct inode *ip, struct inode *ic)
{
  ilock_ext(ic, 0);

  if (ic->type != T_DITTO)
    panic("trying to update a \"child\" that is not a ditto block!\n");

  struct buf *bp;
  struct dinode *dic;

  bp = bread(ip->dev, IBLOCK(ip->inum, sb));
  dic = (struct dinode *)bp->data + ic->inum % IPB;
  dic->type = ic->type;
  dic->major = ic->major;
  dic->minor = ic->minor;
  dic->nlink = 1;
  ic->size = ip->size; // 直接沿用 parent size
  dic->size = ic->size;
  dic->child1 = ic->child1;
  dic->child2 = ic->child2;
  ic->checksum = ip->checksum; // 直接沿用 parent checksum
  dic->checksum = ic->checksum;
  memmove(dic->addrs, ic->addrs, sizeof(ic->addrs));
  log_write(bp);
  brelse(bp);

  iunlock(ic);
}

void iupdate_ext(struct inode *ip, uint skip)
{
  struct buf *bp;
  struct dinode *dip;

  bp = bread(ip->dev, IBLOCK(ip->inum, sb));
  dip = (struct dinode *)bp->data + ip->inum % IPB;
  dip->type = ip->type;
  dip->major = ip->major;
  dip->minor = ip->minor;
  dip->nlink = ip->nlink;
  dip->size = ip->size;

  dip->child1 = ip->child1;
  dip->child2 = ip->child2;
  ip->checksum = ichecksum(ip);
  /* if (ip->checksum != dip->checksum)
    cprintf("	[I] updating checksum of inode %d from %x to %x.\n", ip->inum, dip->checksum, ip->checksum); // */
  
  dip->checksum = ip->checksum;
  memmove(dip->addrs, ip->addrs, sizeof(ip->addrs));
  log_write(bp);
  brelse(bp);

  // Update children
  if (skip == 0)
  {
    if (ip->child1)
      cupdate(ip, iget(ip->dev, ip->child1));
    if (ip->child2)
      cupdate(ip, iget(ip->dev, ip->child2));
  }
}
// Find the inode with number inum on device dev
// and return the in-memory copy. Does not lock
// the inode and does not read it from disk.
struct inode*
iget(uint dev, uint inum)
{
  struct inode *ip, *empty;

  acquire(&icache.lock);

  // Is the inode already cached?
  empty = 0;
  for(ip = &icache.inode[0]; ip < &icache.inode[NINODE]; ip++){
    if(ip->ref > 0 && ip->dev == dev && ip->inum == inum){
      ip->ref++;
      release(&icache.lock);
      return ip;
    }
    if(empty == 0 && ip->ref == 0)    // Remember empty slot.
      empty = ip;
  }

  // Recycle an inode cache entry.
  if(empty == 0)
    panic("iget: no inodes");

  ip = empty;
  ip->dev = dev;
  ip->inum = inum;
  ip->ref = 1;
  ip->valid = 0;
  release(&icache.lock);

  return ip;
}

// Increment reference count for ip.
// Returns ip to enable ip = idup(ip1) idiom.
struct inode*
idup(struct inode *ip)
{
  acquire(&icache.lock);
  ip->ref++;
  release(&icache.lock);
  return ip;
}

// Lock the given inode.
// Reads the inode from disk if necessary.
int
ilock(struct inode *ip)
{
  return ilock_ext(ip, 1);
}

// Reads the given inode, from disk if necessary,
// Recovering its data in a transaction if necessary.
// Guaranteed to return a locked inode OR panic, if the
// file is recoverable.
int ilock_trans(struct inode *ip)
{
  int r = ilock(ip);

  struct inode *ic;

  if (r == 0)
    return 0;

  if (r == E_CORRUPTED)
    return E_CORRUPTED;

  if (r > 0)
  {
    ic = iget(ip->dev, r);
    irescue(ip, ic);
  }

  r = ilock(ip);

  if (r == 0)
    return 0;

  panic("ilock_trans attempted to recover but still failed to unlock");
}

int ilock_ext(struct inode *ip, int checksum)
{
  struct buf *bp;
  struct dinode *dip;

  if (ip == 0 || ip->ref < 1)
    panic("ilock");

  acquiresleep(&ip->lock);

  if (ip->valid == 0)
  {
    bp = bread(ip->dev, IBLOCK(ip->inum, sb));
    dip = (struct dinode *)bp->data + ip->inum % IPB;
    ip->type = dip->type;
    ip->major = dip->major;
    ip->minor = dip->minor;
    ip->nlink = dip->nlink;
    ip->size = dip->size;

    ip->child1 = dip->child1;
    ip->child2 = dip->child2;
    ip->checksum = dip->checksum;

    memmove(ip->addrs, dip->addrs, sizeof(ip->addrs));
    brelse(bp);

    // Initialize some checking variables
    uint replica = REPLICA_SELF;
    ushort rinum;
    struct inode *rinode;

    if (checksum == 0)
      goto zc_success;

  zc_verify:
    if (ichecksum(ip) == ip->checksum)
    {
      goto zc_success;
    }
    else
    {
      replica++;

      // Does replica exist?
      if (replica == REPLICA_CHILD_1)
        rinum = ip->child1;
      else if (replica == REPLICA_CHILD_2)
        rinum = ip->child2;
      else
        goto zc_failure;

      if (!rinum)
        goto zc_failure;

      // Obtain and grab a lock on rinode.
      rinode = iget(ip->dev, rinum);

      if (ilock(rinode) == 0)
      {
        iunlock(rinode);
        iunlock(ip);
        return rinum;
      }

      // Try to verify again...
      goto zc_verify;
    }
  zc_failure:
    /* cprintf("============================\n");
        cprintf("The inum: %d \n", ip->inum);
        cprintf("Inode Type: %d \n", ip->type);
        cprintf("Checksum in inode: %x \n",ip->checksum);
        cprintf("Computed checksum: %x \n", ichecksum(ip));
        cprintf("============================\n"); */
    iunlock(ip);
    return E_CORRUPTED;

  zc_success:
    /*    cprintf("[inum %d] the checksums MATCHED\n    ip->c = %p  == c() = %p\n",
      ip->inum, ip->checksum, ichecksum(ip)); // */

    ip->valid = 1;
    if (ip->type == 0)
      panic("ilock: no type");
  }

  return 0;
}

// Unlock the given inode.
void
iunlock(struct inode *ip)
{
  if(ip == 0 || !holdingsleep(&ip->lock) || ip->ref < 1)
    panic("iunlock");

  releasesleep(&ip->lock);
}

// Drop a reference to an in-memory inode.
// If that was the last reference, the inode cache entry can
// be recycled.
// If that was the last reference and the inode has no links
// to it, free the inode (and its content) on disk.
// All calls to iput() must be inside a transaction in
// case it has to free the inode.
void
iput(struct inode *ip)
{
  acquiresleep(&ip->lock);
  if(ip->valid && ip->nlink == 0){
    acquire(&icache.lock);
    int r = ip->ref;
    release(&icache.lock);
    if(r == 1){
      // inode has no links and no other references: truncate and free.
      itrunc(ip);
      ip->type = 0;
      iupdate(ip);
      ip->valid = 0;
    }
  }
  releasesleep(&ip->lock);

  acquire(&icache.lock);
  ip->ref--;
  release(&icache.lock);
}

// Common idiom: unlock, then put.
void
iunlockput(struct inode *ip)
{
  iunlock(ip);
  iput(ip);
}

void irescue(struct inode *ip, struct inode *rinode)
{

  int max = ((LOGSIZE - 1 - 1 - 2) / 4) * 512;
  int i = 0;
  uint off = 0;

  ilock_ext(rinode, 0);
  ilock_ext(ip, 0);

  int n = ip->size;

  while (i < n)
  {
    int n1 = n - i;
    if (n1 > max)
      n1 = max;

    begin_op();
    // cprintf("[%d] irescue: Calling iduplicate on %d with off = %d, n = %d.\n", rinode->inum, ip->inum, off, n1);
    iduplicate(rinode, ip, off, n1);
    end_op();

    off += n1;
    i += n1;
  }

  iunlock(rinode);
  iunlock(ip);
}

void iduplicate(struct inode *src, struct inode *dst, uint off, uint ntotal)
{
  char buf[512];

  uint n = sizeof(buf);
  memset((void *)buf, 0, n);
  uint r;
  uint _off = off;

  dst->checksum = src->checksum;
  dst->size = src->size;

  while (((r = readi(src, buf, off, n)) > 0) && (off < (ntotal + _off)))
  {
    // cprintf("[%d] iduplicate: Calling writei on %d with off = %d, n = %d.\n", src->inum, dst->inum, off, n); // */
    writei_ext(dst, buf, off, r, 1);
    off += r;
    memset((void *)buf, 0, n);
  }
}

//PAGEBREAK!
// Inode content
//
// The content (data) associated with each inode is stored
// in blocks on the disk. The first NDIRECT block numbers
// are listed in ip->addrs[].  The next NINDIRECT blocks are
// listed in block ip->addrs[NDIRECT].

// Return the disk block address of the nth block in inode ip.
// If there is no such block, bmap allocates one.
static uint
bmap(struct inode *ip, uint bn)
{
  uint addr, *a;
  struct buf *bp;

  if(bn < NDIRECT){
    if((addr = ip->addrs[bn]) == 0)
      ip->addrs[bn] = addr = balloc(ip->dev);
    return addr;
  }
  bn -= NDIRECT;

  if(bn < NINDIRECT){
    // Load indirect block, allocating if necessary.
    if((addr = ip->addrs[NDIRECT]) == 0)
      ip->addrs[NDIRECT] = addr = balloc(ip->dev);
    bp = bread(ip->dev, addr);
    a = (uint*)bp->data;
    if((addr = a[bn]) == 0){
      a[bn] = addr = balloc(ip->dev);
      log_write(bp);
    }
    brelse(bp);
    return addr;
  }

  panic("bmap: out of range");
}

// Truncate inode (discard contents).
// Only called when the inode has no links
// to it (no directory entries referring to it)
// and has no in-memory reference to it (is
// not an open file or current directory).
static void
itrunc(struct inode *ip)
{
  int i, j;
  struct buf *bp;
  uint *a;

  for(i = 0; i < NDIRECT; i++){
    if(ip->addrs[i]){
      bfree(ip->dev, ip->addrs[i]);
      ip->addrs[i] = 0;
    }
  }

  if(ip->addrs[NDIRECT]){
    bp = bread(ip->dev, ip->addrs[NDIRECT]);
    a = (uint*)bp->data;
    for(j = 0; j < NINDIRECT; j++){
      if(a[j])
        bfree(ip->dev, a[j]);
    }
    brelse(bp);
    bfree(ip->dev, ip->addrs[NDIRECT]);
    ip->addrs[NDIRECT] = 0;
  }

  ip->size = 0;
  iupdate(ip);
}

// Copy stat information from inode.
// Caller must hold ip->lock.
void
stati(struct inode *ip, struct stat *st)
{
  st->dev = ip->dev;
  st->ino = ip->inum;
  st->type = ip->type;
  st->nlink = ip->nlink;
  st->size = ip->size;

  st->child1 = ip->child1;
	st->child2 = ip->child2;
	st->checksum = ip->checksum;
}

//PAGEBREAK!
// Read data from inode.
// Caller must hold ip->lock.
int
readi(struct inode *ip, char *dst, uint off, uint n)
{
  uint tot, m;
  struct buf *bp;

  if(ip->type == T_DEV){
    if(ip->major < 0 || ip->major >= NDEV || !devsw[ip->major].read)
      return -1;
    return devsw[ip->major].read(ip, dst, n);
  }

  if(off > ip->size || off + n < off)
    return -1;
  if(off + n > ip->size)
    n = ip->size - off;

  for(tot=0; tot<n; tot+=m, off+=m, dst+=m){
    bp = bread(ip->dev, bmap(ip, off/BSIZE));
    m = min(n - tot, BSIZE - off%BSIZE);
    memmove(dst, bp->data + off%BSIZE, m);
    brelse(bp);
  }
  return n;
}

// PAGEBREAK!
// Write data to inode.
//這個函式修改過了
int
writei (struct inode *ip, char *src, uint off, uint n)
{
  return writei_ext(ip, src, off, n, 0);
}


// Extensible version of writei which, when the skip flag is set,
//   overrides writing to the children of an inode.
//這個函式是新增的
int
writei_ext(struct inode *ip, char *src, uint off, uint n, uint skip)
{
  uint tot, m;
  struct buf *bp;
  char *_src = src;
  uint _off = off;


  if(ip->type == T_DEV){
    if(ip->major < 0 || ip->major >= NDEV || !devsw[ip->major].write)
      return -1;
    return devsw[ip->major].write(ip, src, n);
  }

  if(off > ip->size || off + n < off)
    return -1;
  if(off + n > MAXFILE*BSIZE)
    return -1;

  for(tot=0; tot<n; tot+=m, off+=m, src+=m){
    bp = bread(ip->dev, bmap(ip, off/BSIZE));
    m = min(n - tot, BSIZE - off%BSIZE);
    memmove(bp->data + off%BSIZE, src, m);
    log_write(bp);
    brelse(bp);
  }
  // Update ditto blocks
  struct inode *ci;

  if (skip == 0) {
    if (ip->child1) {
      ci = iget(ip->dev, ip->child1);
      ilock_ext(ci, 0);
      writei(ci, _src, _off, n);
      iunlock(ci);
    }

    if (ip->child2) {
      ci = iget(ip->dev, ip->child2);
      ilock_ext(ci, 0);
      writei(ci, _src, _off, n);
      iunlock(ci);
    }
  }

  // For ditto blocks, the parent iupdate call takes care of updating it
  if (ip->type == T_DITTO)
    return n;

  // An alternative is to do ip->type != T_DEV
  if (n > 0 && off > ip->size)
    ip->size = off;

  if (ip->type != T_DEV)
    iupdate_ext(ip, skip);

  return n;
}

//PAGEBREAK!
// Directories

int
namecmp(const char *s, const char *t)
{
  return strncmp(s, t, DIRSIZ);
}

// Look for a directory entry in a directory.
// If found, set *poff to byte offset of entry.
struct inode*
dirlookup(struct inode *dp, char *name, uint *poff)
{
  uint off, inum;
  struct dirent de;

  if(dp->type != T_DIR)
    panic("dirlookup not DIR");

  for(off = 0; off < dp->size; off += sizeof(de)){
    if(readi(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
      panic("dirlookup read");
    if(de.inum == 0)
      continue;
    if(namecmp(name, de.name) == 0){
      // entry matches path element
      if(poff)
        *poff = off;
      inum = de.inum;
      return iget(dp->dev, inum);
    }
  }

  return 0;
}

// Write a new directory entry (name, inum) into the directory dp.
int
dirlink(struct inode *dp, char *name, uint inum)
{
  int off;
  struct dirent de;
  struct inode *ip;

  // Check that name is not present.
  if((ip = dirlookup(dp, name, 0)) != 0){
    iput(ip);
    return -1;
  }

  // Look for an empty dirent.
  for(off = 0; off < dp->size; off += sizeof(de)){
    if(readi(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
      panic("dirlink read");
    if(de.inum == 0)
      break;
  }

  strncpy(de.name, name, DIRSIZ);
  de.inum = inum;
  if(writei(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
    panic("dirlink");

  return 0;
}

//PAGEBREAK!
// Paths

// Copy the next path element from path into name.
// Return a pointer to the element following the copied one.
// The returned path has no leading slashes,
// so the caller can check *path=='\0' to see if the name is the last one.
// If no name to remove, return 0.
//
// Examples:
//   skipelem("a/bb/c", name) = "bb/c", setting name = "a"
//   skipelem("///a//bb", name) = "bb", setting name = "a"
//   skipelem("a", name) = "", setting name = "a"
//   skipelem("", name) = skipelem("////", name) = 0
//
static char*
skipelem(char *path, char *name)
{
  char *s;
  int len;

  while(*path == '/')
    path++;
  if(*path == 0)
    return 0;
  s = path;
  while(*path != '/' && *path != 0)
    path++;
  len = path - s;
  if(len >= DIRSIZ)
    memmove(name, s, DIRSIZ);
  else {
    memmove(name, s, len);
    name[len] = 0;
  }
  while(*path == '/')
    path++;
  return path;
}

// Look up and return the inode for a path name.
// If parent != 0, return the inode for the parent and copy the final
// path element into name, which must have room for DIRSIZ bytes.
// Must be called inside a transaction since it calls iput().
static struct inode*
namex(char *path, int nameiparent, char *name, int trans)
{
  struct inode *ip, *next;

  if(*path == '/')
    ip = iget(ROOTDEV, ROOTINO);
  else
    ip = idup(myproc()->cwd);

  while((path = skipelem(path, name)) != 0){
	  if (trans) {
      if (ilock_trans(ip) != 0) return 0; // Failed to recover and lock
    } else {
      if (ilock(ip) != 0) return 0; // Failed to lock
    }

    if(ip->type != T_DIR){
      iunlockput(ip);
      return 0;
    }
    if(nameiparent && *path == '\0'){
      // Stop one level early.
      iunlock(ip);
      return ip;
    }
    if((next = dirlookup(ip, name, 0)) == 0){
      iunlockput(ip);
      return 0;
    }
    iunlockput(ip);
    ip = next;
  }
  if(nameiparent){
    iput(ip);
    return 0;
  }
  return ip;
}

struct inode*
namei_ext(char *path, int trans)
{
  char name[DIRSIZ];
  return namex(path, 0, name, trans);
}

struct inode*
nameiparent_ext(char *path, char *name, int trans)
{
  return namex(path, 1, name, trans);
}

struct inode*
namei(char *path)
{
  return namei_ext(path, 0);
}

struct inode*
nameiparent(char *path, char *name)
{
  return nameiparent_ext(path, name, 0);
}

struct inode*
namei_trans(char *path)
{
  return namei_ext(path, 1);
}

struct inode*
nameiparent_trans(char *path, char *name)
{
  return nameiparent_ext(path, name, 1);
}

int
distance_to_root(char *path){
    char name[DIRSIZ];
    struct inode *dp, *ip;
    uint inum1,inum2;
    uint off;
    dp = nameiparent_ext(path, name, 1);
    ilock_trans(dp);
    int counter = 1;
    while((ip = dirlookup(dp,"..", &off) ) != 0){
	inum1 = dp->inum;
	iunlockput(dp);
	dp = ip;
	ilock_trans(dp);
	inum2 = dp->inum;
	//If this is the root.
	if(inum1 == inum2){
	    iunlockput(dp);
	    break;
	}
	counter++;
	off = 0;
    }
    return counter;
}
