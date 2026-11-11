// GEM (GemCoin) PoW ticket grinder.
// preimage = abi.encode(epochSeed(bytes32), wallet(address), nonce(uint256)) = 96 bytes,
// single Keccak-256 block (rate 136). Win: uint256(keccak256(preimage)) <= epochTarget.
// Lanes 0..7 (seed + padded wallet) and padding are folded into BASE; per hash only
// nonce lanes 10..11 change -> 1 permutation per hash.
// usage: miner seed_hex wallet_hex target_hex want threads outfile start_nonce budget_seconds
//    or: miner --digest seed_hex wallet_hex nonce_dec   (validation: print puzzleHash)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>
#include <unistd.h>

static const uint64_t RC[24] = {
 0x0000000000000001ULL,0x0000000000008082ULL,0x800000000000808aULL,0x8000000080008000ULL,
 0x000000000000808bULL,0x0000000080000001ULL,0x8000000080008081ULL,0x8000000000008009ULL,
 0x000000000000008aULL,0x0000000000000088ULL,0x0000000080008009ULL,0x000000008000000aULL,
 0x000000008000808bULL,0x800000000000008bULL,0x8000000000008089ULL,0x8000000000008003ULL,
 0x8000000000008002ULL,0x8000000000000080ULL,0x000000000000800aULL,0x800000008000000aULL,
 0x8000000080008081ULL,0x8000000000008080ULL,0x0000000080000001ULL,0x8000000080008008ULL};

static inline uint64_t rol(uint64_t x, int n){ return n==0?x:((x<<n)|(x>>(64-n))); }

static void keccakf(uint64_t st[25]){
  for(int round=0; round<24; round++){
    uint64_t C[5], D[5], B[25];
    for(int x=0;x<5;x++) C[x]=st[x]^st[x+5]^st[x+10]^st[x+15]^st[x+20];
    for(int x=0;x<5;x++) D[x]=C[(x+4)%5]^rol(C[(x+1)%5],1);
    for(int i=0;i<25;i++) st[i]^=D[i%5];
    static const int r_by_xy[5][5] = {{0,36,3,41,18},{1,44,10,45,2},{62,6,43,15,61},{28,55,25,21,56},{27,20,39,8,14}};
    for(int x=0;x<5;x++) for(int y=0;y<5;y++){
      B[y + 5*((2*x+3*y)%5)] = rol(st[x+5*y], r_by_xy[x][y]);
    }
    for(int y=0;y<5;y++) for(int x=0;x<5;x++){
      st[x+5*y] = B[x+5*y] ^ ((~B[(x+1)%5+5*y]) & B[(x+2)%5+5*y]);
    }
    st[0] ^= RC[round];
  }
}

static uint64_t BASE[25];
static uint64_t TGT[4]; // target as little-endian words, TGT[3] = most significant
static atomic_int found_count;
static atomic_ullong total_tried;
static atomic_int stop_flag;
static int want_count;
static long budget_seconds;
static struct timespec T0;
static FILE* outf;

static void u256_to_words_le(const uint8_t b[32], uint64_t w[4]){
  for(int i=0;i<4;i++){ uint64_t x=0; for(int j=0;j<8;j++) x |= (uint64_t)b[31-(i*8+j)] << (8*j); w[i]=x; }
}
static void setup_base(const uint8_t pre[96], const uint8_t target_be[32]){
  uint64_t st[25]={0};
  for(int i=0;i<12;i++){ uint64_t w=0; for(int j=0;j<8;j++) w |= (uint64_t)pre[i*8+j] << (8*j); st[i]=w; }
  // undo nonce lanes (8..11) — BASE keeps only seed+wallet (lanes 0..7) and padding
  for(int i=8;i<12;i++) st[i]=0;
  st[12] ^= 0x01ULL;                    // suffix 0x01 at byte 96 -> lane 12 byte 0
  st[16] ^= 0x8000000000000000ULL;      // final pad bit at byte 135 -> lane 16 byte 7
  memcpy(BASE, st, sizeof(BASE));
  u256_to_words_le(target_be, TGT);
}
static inline int digest_le_target(const uint64_t st[25]){
  uint64_t top[4]; top[0]=__builtin_bswap64(st[0]); top[1]=__builtin_bswap64(st[1]); top[2]=__builtin_bswap64(st[2]); top[3]=__builtin_bswap64(st[3]);
  uint64_t tt[4]; tt[0]=TGT[3]; tt[1]=TGT[2]; tt[2]=TGT[1]; tt[3]=TGT[0];
  for(int i=0;i<4;i++){ if(top[i]<tt[i]) return 1; if(top[i]>tt[i]) return 0; }
  return 1; // equal counts as <= target
}
typedef struct { int id; int stride; uint64_t start; } warg;
static void* worker(void* p){
  warg* a=(warg*)p;
  uint64_t st[25];
  uint64_t counter = (uint64_t)a->id;
  uint64_t local=0;
  while(!atomic_load(&stop_flag) && atomic_load(&found_count) < want_count){
    __uint128_t nonce = (__uint128_t)a->start + counter;
    memcpy(st, BASE, sizeof(st));
    // nonce big-endian bytes 64..95; low 64 bits -> bytes 88..95 -> lane 11 (LE) = bswap64(lo)
    // bits 64..127 -> bytes 80..87 -> lane 10 = bswap64(hi); lanes 8,9 stay 0 for nonce < 2^128
    st[11] ^= __builtin_bswap64((uint64_t)nonce);
    st[10] ^= __builtin_bswap64((uint64_t)(nonce >> 64));
    keccakf(st);
    local++;
    if(digest_le_target(st)){
      int n = atomic_fetch_add(&found_count, 1) + 1;
      fprintf(outf, "FOUND %llu\n", (unsigned long long)(uint64_t)nonce); fflush(outf);
      printf("FOUND %llu (%d/%d)\n", (unsigned long long)(uint64_t)nonce, n, want_count); fflush(stdout);
    }
    counter += a->stride;
    if((local & 0xFFFF)==0){
      atomic_fetch_add(&total_tried, local); local=0;
      if(budget_seconds > 0){
        struct timespec now; clock_gettime(CLOCK_MONOTONIC,&now);
        if(now.tv_sec - T0.tv_sec >= budget_seconds) atomic_store(&stop_flag, 1);
      }
    }
  }
  atomic_fetch_add(&total_tried, local);
  return NULL;
}

static int hexval2(char c){ if(c>='0'&&c<='9') return c-'0'; if(c>='a'&&c<='f') return c-'a'+10; if(c>='A'&&c<='F') return c-'A'+10; return 0; }
static void parse_hex(const char* s, uint8_t* out, int nbytes){
  if(s[0]=='0'&&(s[1]=='x'||s[1]=='X')) s+=2;
  int len = (int)strlen(s); int start = len - 2*nbytes; // right-align: short strings get leading zero nibbles
  for(int i=0;i<nbytes;i++){
    int hi_idx = start + 2*i, lo_idx = hi_idx + 1;
    int hi = hi_idx >= 0 && hi_idx < len ? hexval2(s[hi_idx]) : 0;
    int lo = lo_idx >= 0 && lo_idx < len ? hexval2(s[lo_idx]) : 0;
    out[i]=(uint8_t)(hi*16+lo);
  }
}
static void build_preimage(const char* seed_hex, const char* wallet_hex, uint8_t pre[96]){
  memset(pre, 0, 96);
  uint8_t seed[32]; parse_hex(seed_hex, seed, 32); memcpy(pre, seed, 32);
  uint8_t wal[20]; parse_hex(wallet_hex, wal, 20); memcpy(pre+44, wal, 20);
}
int main(int argc, char** argv){
  if(argc>=2 && strcmp(argv[1],"--digest")==0){
    // --digest seed wallet nonce_dec -> print puzzleHash hex (validation mode)
    uint8_t pre[96]; build_preimage(argv[2], argv[3], pre);
    uint64_t nonce = strtoull(argv[4], NULL, 10);
    for(int i=0;i<8;i++) pre[64+31-i]=(uint8_t)(nonce>>(8*i));
    uint64_t st[25]={0};
    for(int i=0;i<12;i++){ uint64_t w=0; for(int j=0;j<8;j++) w|=(uint64_t)pre[i*8+j]<<(8*j); st[i]=w; }
    st[12]^=0x01ULL; st[16]^=0x8000000000000000ULL; keccakf(st);
    printf("0x"); for(int i=0;i<4;i++){ uint64_t w=st[i]; for(int j=0;j<8;j++) printf("%02x",(uint8_t)(w>>(8*j))); } printf("\n");
    return 0;
  }
  if(argc<9){ fprintf(stderr,"usage: miner seed_hex wallet_hex target_hex want threads outfile start_nonce budget_seconds\n"); return 2; }
  uint8_t pre[96]; build_preimage(argv[1], argv[2], pre);
  uint8_t tgt[32]; parse_hex(argv[3], tgt, 32);
  want_count = atoi(argv[4]); int T = atoi(argv[5]);
  outf = fopen(argv[6], "a"); if(!outf){ perror("outfile"); return 2; }
  uint64_t start = strtoull(argv[7], NULL, 10);
  budget_seconds = atol(argv[8]);
  setup_base(pre, tgt);
  clock_gettime(CLOCK_MONOTONIC,&T0);
  pthread_t th[16]; warg args[16];
  for(int i=0;i<T;i++){ args[i].id=i; args[i].stride=T; args[i].start=start; pthread_create(&th[i],NULL,worker,&args[i]); }
  for(int i=0;i<T;i++) pthread_join(th[i],NULL);
  struct timespec t1; clock_gettime(CLOCK_MONOTONIC,&t1);
  double dt=(t1.tv_sec-T0.tv_sec)+(t1.tv_nsec-T0.tv_nsec)/1e9;
  printf("DONE found=%d tried=%llu elapsed=%.1fs rate=%.0f H/s\n", atomic_load(&found_count),
         (unsigned long long)atomic_load(&total_tried), dt, dt>0 ? atomic_load(&total_tried)/dt : 0);
  fprintf(outf, "# DONE found=%d tried=%llu elapsed=%.1fs rate=%.0f\n", atomic_load(&found_count),
         (unsigned long long)atomic_load(&total_tried), dt, dt>0 ? atomic_load(&total_tried)/dt : 0);
  fclose(outf);
  return 0;
}
