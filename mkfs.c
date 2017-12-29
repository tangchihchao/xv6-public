#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <assert.h>

#define stat xv6_stat // avoid clash with host struct stat
#include "types.h"
#include "fs.h"
#include "stat.h"
#include "param.h"

#ifndef static_assert
#define static_assert(a, b) do {switch (0) case 0 : case (a):; } while (0)
#endif

#define NINODES 200

// Disk layout:
// [boot block | sb block | log | inode blocks | free bit map | data blocks]

int nbitmap = FSSIZE / (BSIZE * 8) + 1;
int ninodeblocks = NINODES / IPB + 1;
int nlog = LOGSIZE;
int nmeta;   // Number of meta blocks (boot, sb, nlog, inode, bitmap)
int nblocks; // Number of data blocks

int fsfd;
struct superblock sb;
char zeroes[BSIZE];
uint freeinode = 1;
uint freeblock;

void balloc(int);
void wsect(uint, void *);
void winode(uint, struct dinode *);
void rinode(uint inum, struct dinode *ip);
void rsect(uint sec, void *buf);
uint ialloc(ushort type);
void iappend(uint inum, void *p, int n);
uint ichecksum(struct dinode *din);
void rblock(struct dinode *din, uint bn, char *dst);
int readi(struct dinode *din, char *dst, uint off, uint n);
void copy_dinode_content(struct dinode *src, uint dst);

// convert to intel byte order
ushort
xshort(ushort x)
{
  ushort y;
  uchar *a = (uchar *)&y;
  a[0] = x;
  a[1] = x >> 8;
  return y;
}

uint xint(uint x)
{
  uint y;
  uchar *a = (uchar *)&y;
  a[0] = x;
  a[1] = x >> 8;
  a[2] = x >> 16;
  a[3] = x >> 24;
  return y;
}

int main(int argc, char *argv[])
{
  int i, cc, fd;
  uint rootino, inum, off;
  struct dirent de;
  char buf[BSIZE];
  struct dinode din, din2;
  unsigned int checksum;

  static_assert(sizeof(int) == 4, "Integers must be 4 bytes!");

  if (argc < 2)
  {
    fprintf(stderr, "Usage: mkfs fs.img files...\n");
    exit(1);
  }

  assert((BSIZE % sizeof(struct dinode)) == 0);
  assert((BSIZE % sizeof(struct dirent)) == 0);

  fsfd = open(argv[1], O_RDWR | O_CREAT | O_TRUNC, 0666);
  if (fsfd < 0)
  {
    perror(argv[1]);
    exit(1);
  }

  // 1 fs block = 1 disk sector
  nmeta = 2 + nlog + ninodeblocks + nbitmap;
  nblocks = FSSIZE - nmeta;

  sb.size = xint(FSSIZE);
  sb.nblocks = xint(nblocks);
  sb.ninodes = xint(NINODES);
  sb.nlog = xint(nlog);
  sb.logstart = xint(2);
  sb.inodestart = xint(2 + nlog);
  sb.bmapstart = xint(2 + nlog + ninodeblocks);

  printf("nmeta %d (boot, super, log blocks %u inode blocks %u, bitmap blocks %u) blocks %d total %d\n",
         nmeta, nlog, ninodeblocks, nbitmap, nblocks, FSSIZE);

  freeblock = nmeta; // the first free block that we can allocate

  for (i = 0; i < FSSIZE; i++)
    wsect(i, zeroes);

  memset(buf, 0, sizeof(buf));
  memmove(buf, &sb, sizeof(sb));
  wsect(1, buf);

  rootino = ialloc(T_DIR);
  assert(rootino == ROOTINO);

  bzero(&de, sizeof(de));
  de.inum = xshort(rootino);
  strcpy(de.name, ".");
  iappend(rootino, &de, sizeof(de));

  bzero(&de, sizeof(de));
  de.inum = xshort(rootino);
  strcpy(de.name, "..");
  iappend(rootino, &de, sizeof(de));

  for (i = 2; i < argc; i++)
  {
    assert(index(argv[i], '/') == 0);

    if ((fd = open(argv[i], 0)) < 0)
    {
      perror(argv[i]);
      exit(1);
    }

    // Skip leading _ in name when writing to file system.
    // The binaries are named _rm, _cat, etc. to keep the
    // build operating system from trying to execute them
    // in place of system binaries like rm and cat.
    if (argv[i][0] == '_')
      ++argv[i];

    inum = ialloc(T_FILE);

    bzero(&de, sizeof(de));
    de.inum = xshort(inum);
    strncpy(de.name, argv[i], DIRSIZ);
    iappend(rootino, &de, sizeof(de));

    checksum = 0;
    //fprintf(stderr, "Name of file: %s \n", argv[i]);
    int counter2 = 0;
    char *cbuf = (char *)buf;
    memset((void *)cbuf, 0, sizeof(buf));

    while ((cc = read(fd, buf, sizeof(buf))) > 0)
    {
      counter2 += cc;
      uint i;
      unsigned int *bp = (unsigned int *)buf;
      char *cbuf = (char *)buf;
      memset((void *)cbuf + cc, 0, sizeof(buf) - cc);
      for (i = 0; i < sizeof(buf) / sizeof(uint); i++)
      {
        checksum ^= *bp;
        bp++;
      }
      iappend(inum, buf, cc);
    }

    //fprintf(stderr, "Size of the file: %s is %d bytes \n",argv[i],counter2);
    //fprintf(stderr, "Checksum from fd: %x \n", checksum);
    //Read Inode we just wrote to
    //update its checksum
    rinode(inum, &din2);
    char temp_buf[BSIZE];
    readi(&din2, (char *)temp_buf, 0, BSIZE);
    unsigned int checksum2 = 0;
    checksum2 = ichecksum(&din2);
    //fprintf(stderr,"INODE: %d Checksum computed through ichecksum: %x \n", inum, checksum2);
    din2.checksum = xint(checksum2);
    winode(inum, &din2);

    close(fd);
  }

  // fix size of root inode dir
  // also have to fix the checksum
  rinode(rootino, &din);
  off = xint(din.size);
  off = ((off / BSIZE) + 1) * BSIZE;
  din.size = xint(off);
  checksum = ichecksum(&din);
  din.checksum = xint(checksum);
  winode(rootino, &din);

  //Create ditto blocks for root directory
  rinode(rootino, &din);
  uint ditto_inum1, ditto_inum2;
  struct dinode ditto_din1, ditto_din2;
  ditto_inum1 = ialloc(T_DITTO);
  ditto_inum2 = ialloc(T_DITTO);

  copy_dinode_content(&din, ditto_inum1);
  rinode(ditto_inum1, &ditto_din1);
  ditto_din1.checksum = din.checksum;
  ditto_din1.size = din.size;
  winode(ditto_inum1, &ditto_din1);

  copy_dinode_content(&din, ditto_inum2);
  rinode(ditto_inum2, &ditto_din2);
  ditto_din2.checksum = din.checksum;
  ditto_din2.size = din.size;
  winode(ditto_inum2, &ditto_din2);

  rinode(rootino, &din);
  din.child1 = xshort(ditto_inum1);
  din.child2 = xshort(ditto_inum2);
  winode(rootino, &din);

  // fprintf(stderr, "=======> JOAO: root inode checksum %x \n",xint(din.checksum));
  //writes the bitmap to fs.img
  balloc(freeblock);

  exit(0);
}

void wsect(uint sec, void *buf)
{
  if (lseek(fsfd, sec * BSIZE, 0) != sec * BSIZE)
  {
    perror("lseek");
    exit(1);
  }
  if (write(fsfd, buf, BSIZE) != BSIZE)
  {
    perror("write");
    exit(1);
  }
}

void winode(uint inum, struct dinode *ip)
{
  char buf[BSIZE];
  uint bn;
  struct dinode *dip;

  bn = IBLOCK(inum, sb);
  rsect(bn, buf);
  dip = ((struct dinode *)buf) + (inum % IPB);
  *dip = *ip;
  wsect(bn, buf);
}

void rinode(uint inum, struct dinode *ip)
{
  char buf[BSIZE];
  uint bn;
  struct dinode *dip;

  bn = IBLOCK(inum, sb);
  rsect(bn, buf);
  dip = ((struct dinode *)buf) + (inum % IPB);
  *ip = *dip;
}

void rsect(uint sec, void *buf)
{
  if (lseek(fsfd, sec * BSIZE, 0) != sec * BSIZE)
  {
    perror("lseek");
    exit(1);
  }
  if (read(fsfd, buf, BSIZE) != BSIZE)
  {
    perror("read");
    exit(1);
  }
}

uint ialloc(ushort type)
{
  uint inum = freeinode++;
  struct dinode din;

  bzero(&din, sizeof(din));
  din.type = xshort(type);
  din.nlink = xshort(1);
  din.size = xint(0);
  winode(inum, &din);
  return inum;
}

void balloc(int used)
{
  uchar buf[BSIZE];
  int i;

  printf("balloc: first %d blocks have been allocated\n", used);
  assert(used < BSIZE * 8);
  bzero(buf, BSIZE);
  for (i = 0; i < used; i++)
  {
    buf[i / 8] = buf[i / 8] | (0x1 << (i % 8));
  }
  printf("balloc: write bitmap block at sector %d\n", sb.bmapstart);
  wsect(sb.bmapstart, buf);
}

#define min(a, b) ((a) < (b) ? (a) : (b))

void iappend(uint inum, void *xp, int n)
{
  char *p = (char *)xp;
  uint fbn, off, n1;
  struct dinode din;
  char buf[BSIZE];
  uint indirect[NINDIRECT];
  uint x;

  rinode(inum, &din);
  off = xint(din.size);
  // printf("append inum %d at off %d sz %d\n", inum, off, n);
  while (n > 0)
  {
    fbn = off / BSIZE;
    assert(fbn < MAXFILE);
    if (fbn < NDIRECT)
    {
      if (xint(din.addrs[fbn]) == 0)
      {
        din.addrs[fbn] = xint(freeblock++);
      }
      x = xint(din.addrs[fbn]);
    }
    else
    {
      if (xint(din.addrs[NDIRECT]) == 0)
      {
        din.addrs[NDIRECT] = xint(freeblock++);
      }
      rsect(xint(din.addrs[NDIRECT]), (char *)indirect);
      if (indirect[fbn - NDIRECT] == 0)
      {
        indirect[fbn - NDIRECT] = xint(freeblock++);
        wsect(xint(din.addrs[NDIRECT]), (char *)indirect);
      }
      x = xint(indirect[fbn - NDIRECT]);
    }
    n1 = min(n, (fbn + 1) * BSIZE - off);
    rsect(x, buf);
    bcopy(p, buf + off - (fbn * BSIZE), n1);
    wsect(x, buf);
    n -= n1;
    off += n1;
    p += n1;
  }
  din.size = xint(off);
  winode(inum, &din);
}
int readi(struct dinode *din, char *dst, uint off, uint n)
{
  uint tot, m, fbn;
  char data[BSIZE];
  char *cdata = (char *)data;

  if (xint(din->type) == T_DEV)
  {
    fprintf(stderr, "Reading DEV file. Not implemented in readi in mkfs\n");
    return -1;
  }
  if (off > xint(din->size) || off + n < off)
  {
    return -1;
  }
  if (off + n > xint(din->size))
  {
    n = xint(din->size) - off;
  }

  for (tot = 0; tot < n; tot += m, off += m, dst += m)
  {
    fbn = off / BSIZE;
    rblock(din, fbn, (char *)data);
    m = min(n - tot, BSIZE - off % BSIZE);
    memmove(dst, cdata + off % BSIZE, m);
  }
  return n;
}

void rblock(struct dinode *din, uint bn, char *dst)
{
  uint indirect[NINDIRECT];
  uint addr;
  if (bn < NDIRECT)
  {
    rsect(xint(din->addrs[bn]), dst);
    return;
  }
  bn -= NDIRECT;

  if (bn < NINDIRECT)
  {
    rsect(xint(din->addrs[NDIRECT]), (char *)indirect);
    addr = xint(indirect[bn]);
    rsect(addr, dst);
    return;
  }
}

uint ichecksum(struct dinode *din)
{
  unsigned int buf[512];
  char *cbuf = (char *)buf;
  uint n = sizeof(buf);
  uint off = 0;
  uint r, i;
  unsigned int checksum = 0;
  memset((void *)cbuf, 0, n);
  unsigned int *bp;

  while ((r = readi(din, cbuf, off, n)) > 0)
  {
    off += r;
    bp = (unsigned int *)buf;
    for (i = 0; i < sizeof(buf) / sizeof(uint); i++)
    {
      checksum ^= *bp;
      bp++;
    }
    memset((void *)cbuf, 0, n);
  }

  return checksum;
}

void copy_dinode_content(struct dinode *src, uint dst)
{
  char buf[512];
  char *cbuf = (char *)buf;
  uint n = sizeof(buf);
  uint off = 0;
  uint r;
  memset((void *)cbuf, 0, n);

  while ((r = readi(src, cbuf, off, n)) > 0)
  {
    off += r;
    iappend(dst, cbuf, r);
    memset((void *)cbuf, 0, n);
  }
}