#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <inttypes.h>
#include <string.h>
#include <time.h>
#include <sys/timeb.h>

#ifdef BOINC
    #include "boinc_api.h"
#endif

#ifdef __linux__
	#include <sys/utsname.h>
#endif

#define VERSION "3.05"

#ifdef _WIN64
    const char* OS = "Windows 64-bit";
#elif _WIN32
    const char* OS = "Windows 32-bit";
#elif __APPLE__ || __MACH__
    const char* OS = "Mac OS X";
#elif __FreeBSD__
    const char* OS = "FreeBSD";
#else
    const char* OS = "Other";
#endif

// almost - режим пошуку майже ідеальних кубоїдів
int almost = 0;
// progress - режим із відображенням прогресу
int progress = 0;
// quiet - подавити вивід на stdout
int quiet = 0;
// output - відправити stdout у файл out_%
int output = 0;
// report - створити файл із статистикою задачі rep_%
int report = 0;
// backward - пошук у зворотньому напрямку
int backward = 0;
// skip - вважати такими, що виконані, завдання, для яких є out і немає chk
int skip = 0;
// debug - режим із відображенням факторизації та декомпозицій
int debug = 0;
uint32_t debug_step = 1;
// verbose - режим із виводом результату в stderr
int verbose = 0;
uint32_t verbose_step = 1;

// check sum
uint64_t check_sum = 0;
//uint64_t loopCnt = 0;

#define max(a,b) ((a) > (b) ? a : b)
#define min(a,b) ((a) < (b) ? a : b)
#define sign(x) (x > 0 ? 1 : (x == 0 ? 0 : -1))

#ifndef HAVE_BZERO
    #define bzero(ptr,n) \
    memset(ptr, 0, n)
#endif //HAVE_BZERO

#define xchgu64(a,b) \
do {uint64_t c = *a; *a = *b; *b = c;} while (0)

#define xchgu128(a,b) \
do {__uint128_t c = *a; *a = *b; *b = c;} while (0)

// 6542 простих, менших за 2^16 = 65536
#define SMALL_PRIMES_CNT 6542
uint32_t SmallPrimes[SMALL_PRIMES_CNT];

uint32_t * Primes4k1 = NULL, * Primes4k3 = NULL;
uint32_t p4k1Size = 0, p4k3Size = 0;

long double sqrt2;
const int Step = 4;
const uint64_t MinG = 5;
const uint64_t MaxG = (int64_t)((INT64_MAX - 1) / 4 - 1) * 4 + 1;

struct timeb starttime, endtime;
FILE * fout, * frep, * fchk;

uint32_t block_size = 100000;
typedef struct {uint64_t Number; uint8_t Div1Cnt, Div3Cnt;} TBlock;
TBlock * Block = NULL;
uint32_t bSize = 0;

// Число 6437978455413290825^2 = (5^2 * 13^2 * 17 * 29 * 37 * 41 * 53 * 61 * 73 * 89 * 97)^2
// має найбільшу кількість розкладів на суму двох квадратів серед чисел виду 4k+1, менших за 2^63,
// що факторизуються лише простими виду 4k+1, а саме — 246038 розкладів.
//#define MAX_SQUARES_CNT 246038
// Також він має найбільшу кількість різних дільників виду 4k+1 — 11.
// Тому для зберігання факторизації будь-якого числа, що нас цікавлять, достатньо масиву з 11 елементів
#define MAX_FACTORES_CNT 11
// Число 614889782588491410 = 2*3*5*7*11*13*17*19*23*29*31*37*41*43*47 має найбільшу кількість різних дільників
// серед чисел менших за 2^63, тобто 15. Добуток двох чисел може містити максимум 25 дільників
// якщо друге число є 3749562977351496827 = 53*59*61*67*71*73*79*83*89*97, що додає ще 10 різних дільників

uint32_t max_squares_cnt = 0;

typedef struct { uint64_t Prime, A, B; uint8_t Power ;} TFactor;
TFactor * Factors[MAX_FACTORES_CNT];

//Декомпозиція діагоналі на суми квадратів. Q тримає результат; O та R - робочі
typedef struct { uint64_t A, B;} TSquare;
TSquare * O = NULL, * R = NULL;
typedef struct { uint64_t A, B; __uint128_t AA, BB;} TGirard;
TGirard * Q = NULL;

uint32_t oSize = 0, rSize = 0, qSize = 0;
uint32_t
     pcCnt = 0 // кількість ідеальних кубоїдів
    ,ecCnt = 0 // кількість майже ідеальних кубоїдів з нецілим ребром
    ,fcCnt = 0 // кількість майже ідеальних кубоїдів з нецілою лицьовою діагоналлю
    ,ccCnt = 0 // кількість ідеальних кубоїдів з комплексним ребром
    ,icCnt = 0 // кількість уявних кубоїдів з комплексним ребром
    ,tcCnt = 0 // кількість уявних кубоїдів з комплексною лицьовою діагоналлю
    ,cnCnt = 0 // кількість кандидатів, що потрапили на перевірку
    ,toCnt = 0; // загальна кількість знайдених кубоїдів

uint64_t Ini, Fin, Cur, Task_Ini, Task_Fin;
char repfname[256] = "rep", outfname[256] = "out", chkfname[256] = "chk";

static __inline__ uint64_t string_to_u64(const char * s) {
  uint64_t i;
  char c ;
  int scanned = sscanf(s, "%" SCNu64 "%c", &i, &c);
  if (scanned == 1) return i;
  if (scanned > 1) {
    // TBD about extra data found
    return i;
    }
  // TBD failed to scan;
  return 0;
}

static __inline__ void mul_u64(uint64_t a, uint64_t b, uint64_t *h, uint64_t *l)
{
    __uint128_t c = (__uint128_t)a * (__uint128_t)b;
    *h = c >> 64;
    *l = (uint64_t)c;
}

void u128_to_string(const __uint128_t n, char * s)
{
    uint64_t d4, d3, d2, d1, d0, q;
	const int size = 40; // floor(log10(2^128-1))
    char u[40];
    char * t = u;

	// n = d3*2^96 + d2*2^64 + d1*2^32 + d0
	// n = d3*79228162514264337593543950336 + d2*18446744073709551616 + d1*4294967296 + d0

	// n = d3*79_228162514_264337593_543950336 + d2*18_446744073_709551616 + d1*4_294967296 + d0

	// n = d3*79*10^27 + d3*228162514*10^18 + d3*264337593*10^9 + d3*543950336
	//                 + d2*       18*10^18 + d2*446744073*10^9 + d2*709551616
	//                                      + d1*        4*10^9 + d1*294967296
	//                                                          + d0*000000001

	// define constants

	const uint32_t k3 = 79;
	const uint32_t k2 = 228162514;
	const uint32_t k1 = 264337593;
	const uint32_t k0 = 543950336;

	const uint32_t l2 = 18;
	const uint32_t l1 = 446744073;
	const uint32_t l0 = 709551616;

	const uint32_t m1 = 4;
	const uint32_t m0 = 294967296;

	const uint32_t dec_unit = 1000000000;

    d0 = (uint32_t)n;
    d1 = (uint32_t)(n >> 32);
    d2 = (uint32_t)(n >> 64);
    d3 = n >> 96;

    d0 = (k0 * d3) + (l0 * d2) + (m0 * d1) + d0;
    q  = d0 / dec_unit;
    d0 = d0 % dec_unit;

    d1 = q + (k1 * d3) + (l1 * d2) + (m1 * d1);
    q  = d1 / dec_unit;
    d1 = d1 % dec_unit;

    d2 = q + (k2 * d3) + (l2 * d2);
    q  = d2 / dec_unit;
    d2 = d2 % dec_unit;

    d3 = q + (k3 * d3);
    q  = d3 / dec_unit;
    d3 = d3 % dec_unit;

    d4 = q;

    bzero(t, size); // zero the buffer
	sprintf(t,"%u%.9u%.9u%.9u%.9u",(uint32_t)d4,(uint32_t)d3,(uint32_t)d2,(uint32_t)d1,(uint32_t)d0);

	// trim leading zeros
	while (*t && *t == '0') t++;
	if ( *t == 0x0 ) t--; // in case number = 0

    strcpy(s, t);
}

// Евклідів алгоритм обчислення НСД (Найбільший спільний дільник)
uint64_t gcd(uint64_t a, uint64_t b)
{
    if (!b) return a;
    uint64_t c;
    while (a)
    {
        c = a;
        a = b%a;
        b = c;
    }
    return b;
}

/* Функція обчислює (a*b) % m */
// Модуль m не має перевищувати 2^63
static __inline__ uint64_t mod_mul(uint64_t a, uint64_t b, const uint64_t m)
{
   return (uint64_t)(((__uint128_t)a * b) % m);
}

/* Функція обчислює (a^b) % m */
static __inline__ uint64_t mod_pow(uint64_t a, uint64_t b, const uint64_t m)
{
    uint64_t r = 1;
    while (b > 0) {
        if(b & 1)
            r = mod_mul(r, a, m);
        b = b >> 1;
        a = mod_mul(a, a, m);
    }
    return r;
}

// Miller-Rabin primality test
// This function returns false if n is composite
//and returns false if n is probably prime.
int Miller_Rabin(const uint64_t a, uint64_t d, const uint64_t n)
{
    // Corner cases make sure that n > 4

    // Compute a^d % n
    uint64_t x = mod_pow(a, d, n);

    if (x == 1 || x == n-1) return 1;

    // Keep squaring x while one of the following doesn't happen
    // (i)   d does not reach n-1
    // (ii)  (x^2) % n is not 1
    // (iii) (x^2) % n is not n-1
    while (d != n-1)
    {
        x = mod_mul(x, x, n);
        d *= 2;
        if (x == 1)      return 0;
        if (x == n-1)    return 1;
    }

    // Return composite
    return 0;
}

// It returns false if n is composite and returns true if n
// is probably prime.  k is an input parameter that determines
// accuracy level. Higher value of k indicates more accuracy.
int is_prime(const uint64_t n)
{
    // Corner cases
    //if (n <= 1 || n == 4)  return 0;

    // Trial division by first small primes <= 37
    // All other cases will be tested by Miller-Rabin primality test
    for (int i=0; i<12; i++)
        if (n == SmallPrimes[i]) return 1;

    // Find r such that n = 2^d * r + 1 for some r >= 1
    uint64_t d = n - 1;
    while (!(d % 2)) d /= 2;

    // Iterate given number of 'k' times
    // it is enough to test a = 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, and 37
    // for n < 2^64
    if (!Miller_Rabin(2 , d, n)) return 0;
    if (!Miller_Rabin(3 , d, n)) return 0;
    if (!Miller_Rabin(5 , d, n)) return 0;
    if (!Miller_Rabin(7 , d, n)) return 0;
    if (!Miller_Rabin(11, d, n)) return 0;
    if (!Miller_Rabin(13, d, n)) return 0;
    if (!Miller_Rabin(17, d, n)) return 0;
    if (!Miller_Rabin(19, d, n)) return 0;
    if (!Miller_Rabin(23, d, n)) return 0;
    if (!Miller_Rabin(29, d, n)) return 0;
    if (!Miller_Rabin(31, d, n)) return 0;
    if (!Miller_Rabin(37, d, n)) return 0;
    return 1;
}

static __inline__ uint64_t root4(const uint64_t n)
{
    uint64_t a, b, k = n/4;
    for (uint16_t i=0; ; i++) {
        uint16_t j = SmallPrimes[i];
        a = mod_pow(j, k, n);
        b = mod_mul(a, a, n);
        if (b == n-1)
            return a;
    }
}

static __inline__ void decompose_4kp1(uint64_t n, uint64_t *x, uint64_t *y)
{
    int64_t c, r, s;
    s = rintl(sqrtl(n));
    c = root4(n);
    r = n % c;
    while (c > s) {
      n = c;
      c = r;
      r = n % c;
    };
    (*x) = r;
    (*y) = c;
    if (*x > *y)
        xchgu64(x, y);
}

void factorize_range(void)
{
    uint32_t j, i, k, MaxFactor = rintl(sqrtl(Block[(bSize)-1].Number));
    uint64_t d;
    for (j = 0; j < p4k3Size && Primes4k3[j] <= MaxFactor; j++) {
        d = Primes4k3[j];
        k = Block[0].Number % d;
        if (k) k = d - ((Block[0].Number + d)/4) % d;
        for (i = k; i < bSize; i += d)
            Block[i].Div3Cnt++;
    }
    for (j = 0; j < p4k1Size && Primes4k1[j] <= MaxFactor; j++) {
        d = Primes4k1[j];
        k = Block[0].Number % d;
        if (k) {
            if (Block[0].Number > d)
                k = d - ((Block[0].Number - d)/4) % d;
            else
                k = d + ((d - Block[0].Number)/4) % d;
        }
        for (i = k; i < bSize; i += d)
            Factors[Block[i].Div1Cnt++][i].Prime = d;
    }
    for (i = 0; i < bSize; i++) {
        if (Block[i].Div1Cnt && (Block[i].Number == Factors[0][i].Prime))
            Block[i].Div1Cnt = 0;
        if (Block[i].Div1Cnt && !(Block[i].Div3Cnt)) {
            d = Block[i].Number;
            for (k = 0; k < Block[i].Div1Cnt; k++) {
                while (!(d % Factors[k][i].Prime)) {
                    d /= Factors[k][i].Prime;
                    Factors[k][i].Power++;
                }
            }
            if (d != 1) {
                Factors[Block[i].Div1Cnt++][i].Prime = d;
                Factors[k][i].Power = 1;
            }
        }
    }
}

#define MOD48MASK ((1ULL << 48) - 1)
#define MOD56MASK ((1ULL << 56) - 1)
static __inline__ uint64_t is_square(__uint128_t p)
{
    if ((int64_t)(0xC840C04048404040ULL << (p & 63))>=0) return 0;
    uint64_t m48 = (uint64_t)(p >> 96) + ((uint64_t)(p >> 48) & MOD48MASK) + ((uint64_t)p & MOD48MASK);
    m48 = (m48 & MOD48MASK) + (m48 >> 48);
    m48 = (m48 & MOD48MASK) + (m48 >> 48); //important repetition
    uint64_t res, res1;
    // mod 63 & 65, try to cue the compiler to get out-of-order instructions to use two ALUs
    res = (m48 * 0x4104104104105ULL) & MOD56MASK;
    res1 = (m48 * 0x3F03F03F03F04ULL) & MOD56MASK;
    res = (res << 6) - res;
    res1 += (res1 << 6);
    res >>= 56;
    res1 >>= 56;
    if ((int64_t)(0xC940A2480C124020ULL << res) >= 0) return 0;
    if ((int64_t)(0xC862806619805184ULL << res1) > 0) return 0;
    // mod 17
    res = (m48 * 0xF0F0F0F0F0F10ULL) & MOD56MASK;
    res += (res << 4);
    res >>= 56;
    if ((int64_t)(0xE8C5800000000000ULL << res) >= 0) return 0;
    check_sum++;
    uint64_t c = rintl(sqrtl(p));
    return (p == (__uint128_t)c*(__uint128_t)c) ? c : 0;
}

static __inline__ uint64_t is_sub_of_squares_square_too(__uint128_t a, __uint128_t b)
{
    if (a == b) return 0;
    if (a < b) xchgu128(&a, &b);
    if ((a + 1) & b & 1) return 0;
    return is_square(a - b);
}

static __inline__ uint64_t is_sum_of_squares_square_too(__uint128_t a, __uint128_t b)
{
    if (a & b & 1) return 0;
    return is_square(a + b);
}

static __inline__ void decompose_factors(void)
{
    for (uint32_t i = 0; i < bSize; i++)
        if (!Block[i].Div3Cnt && Block[i].Div1Cnt)
            for (uint8_t j = 0; j < Block[i].Div1Cnt; j++)
                decompose_4kp1(Factors[j][i].Prime, &Factors[j][i].A, &Factors[j][i].B);
}

static __inline__ uint32_t double_powers(void)
{
    uint32_t mi, m = 1;
    for (uint32_t i = 0; i < bSize; i++) {
        if (!Block[i].Div3Cnt && Block[i].Div1Cnt) {
            mi = 1;
            for (int j = 0; j < Block[i].Div1Cnt; j++) {
                Factors[j][i].Power *= 2;
                mi *= Factors[j][i].Power+1;
            }
            mi = (mi+1) / 2;
            if (mi > m) m = mi;
        }
    }
    return m;
}

static __inline__ void produce_R_from_O(TFactor f)
{
    uint64_t x, y;
    for (uint32_t i = 0; i < oSize; i++) {
        x = llabs(O[i].A*f.B - O[i].B*f.A);
        y = O[i].A*f.A + O[i].B*f.B;
        if (x > y)
            xchgu64(&x, &y);
        R[rSize].A = x;
        R[rSize].B = y;
        rSize++;
        x = llabs(O[i].A*f.A - O[i].B*f.B);
        y = O[i].A*f.B + O[i].B*f.A;
        if (x > y)
            xchgu64(&x, &y);
        R[rSize].A = x;
        R[rSize].B = y;
        rSize++;
    }
}

static __inline__ void produce_R_from_Q(TFactor f)
{
    uint64_t x, y;
    for (uint32_t i = 0; i < qSize; i++) {
        x = llabs(Q[i].A*f.B - Q[i].B*f.A);
        y = Q[i].A*f.A + Q[i].B*f.B;
        if (x > y)
            xchgu64(&x, &y);
        R[rSize].A = x;
        R[rSize].B = y;
        rSize++;
        x = llabs(Q[i].A*f.A - Q[i].B*f.B);
        y = Q[i].A*f.B + Q[i].B*f.A;
        if (x > y)
            xchgu64(&x, &y);
        R[rSize].A = x;
        R[rSize].B = y;
        rSize++;
    }
}

static __inline__ void enrich_Q_by_R(void)
{
    int found, addnew;
    for (uint32_t i = 0, j = 0; i < rSize; i++) {
        if (!(i > 0 && R[i].A == R[i-1].A)) {
            found = addnew = 0;
            while (!found && !addnew && j < qSize) {
                found = (Q[j].A == R[i].A && Q[j].B == R[i].B);
                if (!found) {
                    if (Q[j].A < R[i].A) j++;
                    else addnew = 1;
                }
            }
            if (!found) {
                Q[qSize].A = R[i].A;
                Q[qSize].B = R[i].B;
                qSize++;
            }
        }
    }
}

static __inline__ void enrich_O_by_R(void)
{
    int found, addnew;
    for (uint32_t i = 0, j = 0; i < rSize; i++) {
        if (!(i > 0 && R[i].A == R[i-1].A)) {
            found = addnew = 0;
            while (!found && !addnew && j < oSize) {
                found = (O[j].A == R[i].A && O[j].B == R[i].B);
                if (!found) {
                    if (O[j].A < R[i].A) j++;
                    else addnew = 1;
                }
            }
            if (!found) {
                O[oSize].A = R[i].A;
                O[oSize].B = R[i].B;
                oSize++;
            }
        }
    }
}

void sort_squares_by_A(TSquare * s, int32_t l, int32_t h)
{
    int32_t i, j, k;
    TSquare t;
    do {
        i = l;
        j = h;
        k = (l+h) >> 1;
        do {
            while (s[i].A < s[k].A) i++;
            while (s[j].A > s[k].A) j--;
            if (i <= j) {
                t = s[i];
                s[i] = s[j];
                s[j] = t;
                if (k == i) k = j;
                else if (k == j) k = i;
                i++;
                j--;
            }
        } while (i <= j);
        if (l < j) sort_squares_by_A(s, l, j);
        l = i;
    } while (i < h);
}

static __inline__ void copy_squares(void)
{
    for (uint32_t i=0; i < oSize; i++) {
        Q[i].A = O[i].A;
        Q[i].B = O[i].B;
        Q[i].AA = (__uint128_t)Q[i].A * (__uint128_t)Q[i].A;
        Q[i].BB = (__uint128_t)Q[i].B * (__uint128_t)Q[i].B;
    }
    qSize = oSize;
}

void find_all_squares(uint32_t i)
{
    qSize = 0;
    O[0].A = 0;
    O[0].B = 1;
    oSize = 1;
    for (int j = 0; j < Block[i].Div1Cnt ; j++) {
        for (int k = 1; k <= Factors[j][i].Power ; k++) {
            if (k & 1) {
                qSize = 0;
                rSize = 0;
                produce_R_from_O(Factors[j][i]);
                sort_squares_by_A(R, 0, rSize-1);
                enrich_Q_by_R();
            }
            else {
                for (uint32_t l=0; l < oSize; l++) {
                    O[l].A *= Factors[j][i].Prime;
                    O[l].B *= Factors[j][i].Prime;
                }
                rSize = 0;
                produce_R_from_Q(Factors[j][i]);
                sort_squares_by_A(R, 0, rSize-1);
                enrich_O_by_R();
                sort_squares_by_A(O, 0, oSize-1);
            }
        }
    }
    copy_squares();
}

// Сортуємо ребра A, B, C за зростанням
void sort_by_ABC(int64_t A, int64_t B, int64_t C, char * sA, char * sB, char * sC, char * sD, char * sE, char * sF)
{
    char T[36] = "";
    char * sT = T;
    int64_t I;
    if (A > B) {
        strcpy(sT, sA);
        strcpy(sA, sB);
        strcpy(sB, sT);
        strcpy(sT, sF);
        strcpy(sF, sE);
        strcpy(sE, sT);
        I = A;
        A = B;
        B = I;
    }
    if (A > C) {
        strcpy(sT, sA);
        strcpy(sA, sC);
        strcpy(sC, sT);
        strcpy(sT, sF);
        strcpy(sF, sD);
        strcpy(sD, sT);
        I = A;
        A = C;
        C = I;
    }
    if (B > C) {
        strcpy(sT, sB);
        strcpy(sB, sC);
        strcpy(sC, sT);
        strcpy(sT, sE);
        strcpy(sE, sD);
        strcpy(sD, sT);
    }
}

// Сортуємо лицьові діагоналі D, E, F за зростанням
void sort_by_DEF(int64_t D, int64_t E, int64_t F, char * sA, char * sB, char * sC, char * sD, char * sE, char * sF)
{
    char T[36] = "";
    char * sT = T;
    int64_t I;
    if (E > F) {
        strcpy(sT, sA);
        strcpy(sA, sB);
        strcpy(sB, sT);
        strcpy(sT, sF);
        strcpy(sF, sE);
        strcpy(sE, sT);
        I = E;
        E = F;
        F = I;
    }
    if (D > F) {
        strcpy(sT, sA);
        strcpy(sA, sC);
        strcpy(sC, sT);
        strcpy(sT, sF);
        strcpy(sF, sD);
        strcpy(sD, sT);
        I = D;
        D = F;
        F = I;
    }
    if (D > E) {
        strcpy(sT, sB);
        strcpy(sB, sC);
        strcpy(sC, sT);
        strcpy(sT, sE);
        strcpy(sE, sD);
        strcpy(sD, sT);
    }
}

void save_checkpoint(uint64_t pos)
{
    fchk = fopen(chkfname, "w");
    if(fchk == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    struct timeb curtime;
    ftime(&curtime);
    uint64_t dif = (curtime.time - starttime.time) * 1000 + (curtime.millitm - starttime.millitm);
    fprintf(fchk,  "%" PRIu64
                  ",%" PRIu64
                  ",%" PRIu64
                  ",%" PRIu64
                  ",%d,%" PRIu64
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                ,Ini
                ,Fin
                ,pos
                ,check_sum
                ,backward
                ,dif
                ,cnCnt
                ,pcCnt
                ,ecCnt
                ,fcCnt
                ,ccCnt
                ,icCnt
                ,tcCnt
           );
    fflush(fchk);
    fclose(fchk);
#if defined BOINC
	boinc_checkpoint_completed();
#endif
}

int read_checkpoint(void)
{
    fchk = fopen(chkfname, "r");
    if(fchk == NULL)
        return (EXIT_FAILURE);
    char c;
    uint64_t dif;
    int scanned = fscanf(fchk, "%" SCNu64
                              ",%" SCNu64
                              ",%" SCNu64
                              ",%" SCNu64
                              ",%d,%" SCNu64
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%c"
                              , &Ini
                              , &Fin
                              , &Cur
                              , &check_sum
                              , &backward
                              , &dif
                              , &cnCnt
                              , &pcCnt
                              , &ecCnt
                              , &fcCnt
                              , &ccCnt
                              , &icCnt
                              , &tcCnt
                              , &c);
    fclose(fchk);
    if (scanned != 13) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    if (!Cur) return 1;
        else Cur = ((Cur / Step) + 1) * Step + 1;
    starttime.time -= dif / 1000;
    long int millisec = (dif % 1000);
    if (starttime.millitm < millisec) {
        starttime.millitm += 1000 - millisec;
        starttime.time--;
    } else starttime.millitm -= millisec;
    toCnt = pcCnt + ecCnt + fcCnt + ccCnt + icCnt + tcCnt/* + mcCnt*/;
    return 0;
}

void print_extend_out(char * msg, char * A, char * B, char * C, char * D, char * E, char * F, char * G)
{
    fprintf(stderr, "%s\n", msg);
    fprintf(stderr, "A = %s\n", A);
    fprintf(stderr, "B = %s\n", B);
    fprintf(stderr, "C = %s\n", C);
    fprintf(stderr, "D = %s\n", D);
    fprintf(stderr, "E = %s\n", E);
    fprintf(stderr, "F = %s\n", F);
    fprintf(stderr, "G = %s\n", G);
    fprintf(stderr, "-------------------------------------------------\n");
}

void search_almost(uint64_t G)
{
    //Q має бути впорядкованим за A
    uint32_t i, j;
    uint64_t A, B, E, F, K, L, M, N, P, R;
    __uint128_t AA, BB, EE, FF;
    char sA[40], sB[40], sC[40], sD[40], sE[40], sF[40], sG[40];
    char rtsn[] = "√";
    char s128[40];
    for (i = 1; i < qSize-1; i++) {
        A = Q[i].A;
        F = Q[i].B;
        AA = Q[i].AA;
        FF = Q[i].BB;
        for (j = i + 1; j < qSize; j++) {
            B = Q[j].A;
            E = Q[j].B;
            BB = Q[j].AA;
            EE = Q[j].BB;
            K = is_sum_of_squares_square_too(AA, BB);
            L = is_sum_of_squares_square_too(AA, EE);
            M = is_sum_of_squares_square_too(BB, FF);
            N = is_sum_of_squares_square_too(EE, FF);
            P = is_sub_of_squares_square_too(BB, AA);
            R = is_sub_of_squares_square_too(EE, AA);
            if (P) {
                if (gcd(gcd(gcd(A, E), G), P)==1) {
                    if (L) {
                        pcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64, A);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, P);
                        sprintf(sD, "%" PRIu64, L);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(A, E, P, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "P,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "P,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Perfect Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%" PRIu64 "i", P);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64, F);
                        sprintf(sF, "%" PRIu64, L);
                        sort_by_ABC(-A, -P, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64 "i", P);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", F);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, L);
                        sort_by_ABC(-E, -P, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, P);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64 "i", A);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", L);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(-E, -A, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    } else {
                        u128_to_string((__uint128_t)A*(__uint128_t)A + (__uint128_t)E*(__uint128_t)E, s128);
                        fcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64, A);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, P);
                        sprintf(sD, "%s%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(A, E, P, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "F,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "F,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Face Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%" PRIu64 "i", P);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64, F);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-A, -P, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64 "i", P);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", F);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-E, -P, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, P);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64 "i", A);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%s-%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(-E, -A, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
                if (gcd(gcd(gcd(B, F), G), P)==1) {
                    if (M) {
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64 "i", P);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64, A);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, M);
                        sort_by_ABC(-P, B, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64, P);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", A);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, M);
                        sort_by_ABC(-B, P, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, P);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", E);
                        sprintf(sE, "%" PRIu64, A);
                        sprintf(sF, "%" PRIu64, M);
                        sort_by_ABC(-F, P, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, P);
                        sprintf(sA, "%" PRIu64 "i", G);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", E);
                        sprintf(sE, "%" PRIu64 "i", A);
                        sprintf(sF, "%" PRIu64, M);
                        sort_by_ABC(-G, B, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    } else {
                        u128_to_string((__uint128_t)B*(__uint128_t)B + (__uint128_t)F*(__uint128_t)F, s128);
                        icCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64 "i", P);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64, A);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-P, B, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Imaginary Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64, P);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", A);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-B, P, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, P);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", E);
                        sprintf(sE, "%" PRIu64, A);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-F, P, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, P);
                        sprintf(sA, "%" PRIu64 "i", G);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", E);
                        sprintf(sE, "%" PRIu64 "i", A);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-G, B, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
                if (gcd(gcd(gcd(A, B), E), F)==1) {
                    if (R) {
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, E);
                        sprintf(sD, "%" PRIu64, P);
                        sprintf(sE, "%" PRIu64, R);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-A, B, E, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64, A);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", P);
                        sprintf(sE, "%" PRIu64, R);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-B, A, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64, A);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", R);
                        sprintf(sE, "%" PRIu64, P);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-E, A, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, E);
                        sprintf(sD, "%" PRIu64 "i", R);
                        sprintf(sE, "%" PRIu64 "i", P);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-F, B, E, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    } else {
                        u128_to_string((__uint128_t)E*(__uint128_t)E - (__uint128_t)A*(__uint128_t)A, s128);
                        icCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, E);
                        sprintf(sD, "%" PRIu64, P);
                        sprintf(sE, "%s%s", rtsn, s128);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-A, B, E, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Imaginary Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64, A);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", P);
                        sprintf(sE, "%s%s", rtsn, s128);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-B, A, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64, A);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%s-%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, P);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-E, A, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, E);
                        sprintf(sD, "%s-%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64 "i", P);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-F, B, E, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
            }
            if (R) {
                if (gcd(gcd(gcd(A, B), G), R)==1) {
                    if (K) {
                        pcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64, A);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, R);
                        sprintf(sD, "%" PRIu64, K);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(A, B, R, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "P,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "P,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Perfect Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, R);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64 "i", A);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", K);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(-B, -A, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%" PRIu64 "i", R);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", E);
                        sprintf(sE, "%" PRIu64, F);
                        sprintf(sF, "%" PRIu64, K);
                        sort_by_ABC(-A, -R, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64 "i", R);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", F);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, K);
                        sort_by_ABC(-B, -R, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    } else {
                        u128_to_string((__uint128_t)A*(__uint128_t)A + (__uint128_t)B*(__uint128_t)B, s128);
                        fcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64, A);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, R);
                        sprintf(sD, "%s%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(A, B, R, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "F,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "F,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Face Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, R);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64 "i", A);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%s-%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(-B, -A, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%" PRIu64 "i", R);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", E);
                        sprintf(sE, "%" PRIu64, F);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-A, -R, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64 "i", R);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", F);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-B, -R, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
                if (gcd(gcd(gcd(E, F), G), R)==1) {
                    if (N) {
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64 "i", R);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64, A);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_ABC(-R, E, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64, R);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", A);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_ABC(-E, R, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, R);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64, A);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_ABC(-F, R, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, R);
                        sprintf(sA, "%" PRIu64 "i", G);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64 "i", A);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_ABC(-G, E, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    } else {
                        u128_to_string((__uint128_t)E*(__uint128_t)E + (__uint128_t)F*(__uint128_t)F, s128);
                        icCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64 "i", R);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64, A);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-R, E, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Imaginary Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64, R);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", A);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-E, R, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, R);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64, A);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-F, R, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, R);
                        sprintf(sA, "%" PRIu64 "i", G);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64 "i", A);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-G, E, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
                if (gcd(gcd(gcd(A, B), E), F)==1) {
                    if (!P) {
                        u128_to_string((__uint128_t)B*(__uint128_t)B - (__uint128_t)A*(__uint128_t)A, s128);
                        icCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, E);
                        sprintf(sD, "%s%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, R);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-A, B, E, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Imaginary Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64, A);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%s-%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, R);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-B, A, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64, A);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", R);
                        sprintf(sE, "%s%s", rtsn, s128);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-E, A, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, E);
                        sprintf(sD, "%" PRIu64 "i", R);
                        sprintf(sE, "%s-%s", rtsn, s128);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-F, B, E, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
            }
            if (K) {
                if (gcd(gcd(E, F), K)==1) {
                    if (!R) {
                        u128_to_string((__uint128_t)E*(__uint128_t)E - (__uint128_t)A*(__uint128_t)A, s128);
                        ecCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64, A);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%s%s", rtsn, s128);
                        sprintf(sD, "%" PRIu64, K);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_DEF(K, E, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "E,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "E,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Edge Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%s%s", rtsn, s128);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64 "i", A);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", K);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_DEF(-K, E, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%s-%s", rtsn, s128);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", E);
                        sprintf(sE, "%" PRIu64, F);
                        sprintf(sF, "%" PRIu64, K);
                        sort_by_DEF(-E, F, K, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%s-%s", rtsn, s128);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", F);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, K);
                        sort_by_DEF(-F, E, K, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
            }
            if (L) {
                if (gcd(gcd(B, F), L)==1) {
                    if (!P) {
                        u128_to_string((__uint128_t)B*(__uint128_t)B - (__uint128_t)A*(__uint128_t)A, s128);
                        ecCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64, A);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%s%s", rtsn, s128);
                        sprintf(sD, "%" PRIu64, L);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_DEF(L, B, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "E,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "E,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Edge Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%s-%s", rtsn, s128);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64, F);
                        sprintf(sF, "%" PRIu64, L);
                        sort_by_DEF(-B, F, L, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%s-%s", rtsn, s128);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", F);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, L);
                        sort_by_DEF(-F, B, L, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%s%s", rtsn, s128);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64 "i", A);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", L);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_DEF(-L, B, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
            }
            if (M) {
                if (gcd(gcd(A, E), M)==1) {
                    if (!P) {
                        u128_to_string((__uint128_t)B*(__uint128_t)B - (__uint128_t)A*(__uint128_t)A, s128);
                        icCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%s-%s", rtsn, s128);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64, A);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, M);
                        sort_by_DEF(A, E, M, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Imaginary Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%s%s", rtsn, s128);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", A);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, M);
                        sort_by_DEF(-A, E, M, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%s%s", rtsn, s128);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", E);
                        sprintf(sE, "%" PRIu64, A);
                        sprintf(sF, "%" PRIu64, M);
                        sort_by_DEF(-E, A, M, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%s%s", rtsn, s128);
                        sprintf(sA, "%" PRIu64 "i", G);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", E);
                        sprintf(sE, "%" PRIu64 "i", A);
                        sprintf(sF, "%" PRIu64, M);
                        sort_by_DEF(-E, -A, M, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
            }
            if (N) {
                if (gcd(gcd(A, B), N)==1) {
                    if (!R) {
                        u128_to_string((__uint128_t)E*(__uint128_t)E - (__uint128_t)A*(__uint128_t)A, s128);
                        icCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%s-%s", rtsn, s128);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64, A);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_DEF(A, B, N, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Imaginary Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%s%s", rtsn, s128);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", A);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_DEF(-A, B, N, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%s%s", rtsn, s128);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64, A);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_DEF(-B, A, N, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%s%s", rtsn, s128);
                        sprintf(sA, "%" PRIu64 "i", G);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64 "i", A);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_DEF(-B, -A, N, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
            }
        }
    }
}

void search_perfect(uint64_t G)
{
    //Q має бути впорядкованим за A
    uint32_t i, j;
    uint64_t A, B, C, D, E, F, N, P, maxB, minE;
    int16_t A19, B19, C19, GG19 = (G % 19)*(G % 19), FF19;
    int16_t A11, B11, C11, GG11 = (G % 11)*(G % 11), FF11;
    char rtsn[] = "√";
    char s128[40];
    char sA[40], sB[40], sC[40], sD[40], sE[40], sF[40], sG[40];
    // найбільша лицьова діагональ не може бути менша за √2 довжини найменшого ребра
    // залишаємо ще 2 позиції вище у розкладі за найменше ребро
    // для середнього ребра (B) та більшого ребра (С) або лицьової діагоналі (D)
    for (i = 1; i < qSize-2; i++) {
        if (Q[i].A*sqrt2 > Q[i].B) break;
        A = Q[i].A;
        A19 = A % 19;
        FF19 = GG19 - A19*A19;
        A11 = A % 11;
        FF11 = GG11 - A11*A11;
        // найбільша лицьова діагональ не може бути менша за √2 довжини середнього ребра
        maxB = Q[i].B / sqrt2;
        // середня лицьова діагональ не може бути менша за √2 довжини найменшого ребра
        minE = A * sqrt2;
        for (j = i + 1; j < qSize-1; j++) {
            if (Q[j].A > maxB) break;
            if (minE > Q[j].B) break;
            B = Q[j].A;
            // одне із ребер має ділитися на 19
            if (A19) {
                B19 = B % 19;
                C19 = (FF19 - B19*B19) % 19;
                if (B19 && C19) continue;
            }
            // одне із ребер має ділитися на 11
            if (A11) {
                B11 = B % 11;
                C11 = (FF11 - B11*B11) % 11;
                if (B11 && C11) continue;
            }
            //loopCnt++;
            C = is_square(Q[j].BB - Q[i].AA);
            if (C) {
                if (gcd(gcd(gcd(A, B), G), C)==1) {
                    D = is_square(Q[i].AA + Q[j].AA);
                    E = Q[j].B;
                    F = Q[i].B;
                    if (D) {
                        pcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64, A);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, C);
                        sprintf(sD, "%" PRIu64, D);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(A, B, C, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "P,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "P,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Perfect Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    } else {
                        u128_to_string((__uint128_t)A*(__uint128_t)A + (__uint128_t)B*(__uint128_t)B, s128);
                        fcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64, A);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, C);
                        sprintf(sD, "%s%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(A, B, C, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "F,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "F,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Face Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, C);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64 "i", A);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%s-%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%" PRIu64, F);
                        sort_by_ABC(-B, -A, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%" PRIu64 "i", C);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", E);
                        sprintf(sE, "%" PRIu64, F);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-A, -C, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64 "i", C);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", F);
                        sprintf(sE, "%" PRIu64, E);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-B, -C, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                    N = is_square(Q[i].BB + Q[j].BB);
                    if (N) {
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64 "i", C);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64, A);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_ABC(-C, E, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64, C);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", A);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_ABC(-E, C, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, C);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64, A);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_ABC(-F, C, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, C);
                        sprintf(sA, "%" PRIu64 "i", G);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64 "i", A);
                        sprintf(sF, "%" PRIu64, N);
                        sort_by_ABC(-G, E, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    } else {
                        u128_to_string((__uint128_t)E*(__uint128_t)E + (__uint128_t)F*(__uint128_t)F, s128);
                        icCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, G);
                        sprintf(sA, "%" PRIu64 "i", C);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64, A);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-C, E, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Imaginary Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64, C);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", A);
                        sprintf(sE, "%" PRIu64, B);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-E, C, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, C);
                        sprintf(sC, "%" PRIu64, G);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64, A);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-F, C, G, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, C);
                        sprintf(sA, "%" PRIu64 "i", G);
                        sprintf(sB, "%" PRIu64, E);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", B);
                        sprintf(sE, "%" PRIu64 "i", A);
                        sprintf(sF, "%s%s", rtsn, s128);
                        sort_by_ABC(-G, E, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                    P = is_square(Q[j].AA - Q[i].AA);
                    if (P) {
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, E);
                        sprintf(sD, "%" PRIu64, P);
                        sprintf(sE, "%" PRIu64, C);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-A, B, E, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64, A);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", P);
                        sprintf(sE, "%" PRIu64, C);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-B, A, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64, A);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", C);
                        sprintf(sE, "%" PRIu64, P);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-E, A, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        ccCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, E);
                        sprintf(sD, "%" PRIu64 "i", C);
                        sprintf(sE, "%" PRIu64 "i", P);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-F, B, E, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "C,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Complex Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    } else {
                        u128_to_string((__uint128_t)B*(__uint128_t)B - (__uint128_t)A*(__uint128_t)A, s128);
                        icCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, F);
                        sprintf(sA, "%" PRIu64 "i", A);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, E);
                        sprintf(sD, "%s%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, C);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-A, B, E, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "I,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Imaginary Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, E);
                        sprintf(sA, "%" PRIu64 "i", B);
                        sprintf(sB, "%" PRIu64, A);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%s-%s", rtsn, s128);
                        sprintf(sE, "%" PRIu64, C);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-B, A, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, B);
                        sprintf(sA, "%" PRIu64 "i", E);
                        sprintf(sB, "%" PRIu64, A);
                        sprintf(sC, "%" PRIu64, F);
                        sprintf(sD, "%" PRIu64 "i", C);
                        sprintf(sE, "%s%s", rtsn, s128);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-E, A, F, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                        tcCnt++;
                        toCnt++;
                        sprintf(sG, "%" PRIu64, A);
                        sprintf(sA, "%" PRIu64 "i", F);
                        sprintf(sB, "%" PRIu64, B);
                        sprintf(sC, "%" PRIu64, E);
                        sprintf(sD, "%" PRIu64 "i", C);
                        sprintf(sE, "%s-%s", rtsn, s128);
                        sprintf(sF, "%" PRIu64, G);
                        sort_by_ABC(-F, B, E, sA, sB, sC, sD, sE, sF);
                        if (!quiet) fprintf(stdout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (output) fprintf(fout, "T,%s,%s,%s,%s,%s,%s,%s\n", sG, sA, sB, sC, sD, sE, sF);
                        if (verbose && !progress && !(cnCnt % verbose_step))
                            print_extend_out("Twilight Cuboid", sA, sB, sC, sD, sE, sF, sG);
                    }
                }
            }
        }
    }
}

void free_primes(void)
{
    free(Primes4k1);
    free(Primes4k3);
}

void init_primes(void)
{
    uint32_t sq = ceil(sqrtl(Fin)), cb = ceil(sqrtl(sqrtf(Fin)));
    uint32_t sSize = max(ceil((float)sq / 128), SMALL_PRIMES_CNT);
    uint32_t i, j;
    uint64_t * sieve;
    sieve = (uint64_t*) calloc (sSize, sizeof(uint64_t));
    if (sieve == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    sieve[0] = 1;
    for (i = 1; i < sSize; i++) sieve[i] = 0;
    for (i = 3; i <= cb; i += 2) {
        for (j = 3*i; j <= sq; j += 2*i) {
            sieve[j >> 7] |= ((uint64_t)1 << ((j >> 1)&63));
        }
    }
    SmallPrimes[0] = 2;
    j = 1;
    for (i = 3; j < SMALL_PRIMES_CNT ; i += 2) {
        if (!(sieve[i >> 7]&((uint64_t)1 << ((i >> 1)&63))))
            SmallPrimes[j++] = i;
    }
    p4k1Size = 0;
    p4k3Size = 0;
    for (i = 3; i <= sq; i += 2) {
        if (!(sieve[i >> 7]&((uint64_t)1 << ((i >> 1)&63)))) {
            if (i % 4 == 1)
                p4k1Size++;
            else
                p4k3Size++;
        }
    }
    Primes4k1 = (uint32_t*) malloc (sizeof(uint32_t)*p4k1Size);
    if (Primes4k1 == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    Primes4k3 = (uint32_t*) malloc (sizeof(uint32_t)*p4k3Size);
    if (Primes4k3 == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    p4k1Size = 0;
    p4k3Size = 0;
    for (i = 3; i <= sq; i += 2) {
        if (!(sieve[i >> 7]&((uint64_t)1 << ((i >> 1)&63)))) {
            if (i % 4 == 1)
                Primes4k1[p4k1Size++] = i;
            else
                Primes4k3[p4k3Size++] = i;
        }
    }
    free(sieve);
}

void free_block(void)
{
    if (Block != NULL)
        for (uint8_t j = 0; j < MAX_FACTORES_CNT; j++)
            free(Factors[j]);
    free(Block);
}

void init_block(uint32_t size)
{
    free_block();
    bSize = size;
    Block = (TBlock *) calloc(size, sizeof(TBlock));
    if (Block == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    for (uint8_t j = 0; j < MAX_FACTORES_CNT; j++) {
        Factors[j] = (TFactor *) calloc(size, sizeof(TFactor));
        if (Factors[j] == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
    }

    uint64_t n = Cur;
    for (uint32_t i = 0; i < size; i++) {
        Block[i].Number = n;
        n += 4;
    }
}

void free_squares(void)
{
    free(O);
    free(R);
    free(Q);
}

void init_squares(uint32_t size)
{
    if (size > max_squares_cnt) {
        max_squares_cnt = size;
        O = (TSquare *) calloc(size, sizeof(TSquare));
        if (O == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
        R = (TSquare *) calloc(2*size, sizeof(TSquare));
        if (R == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
        Q = (TGirard *) calloc(size, sizeof(TGirard));
        if (Q == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
    }
}

int init_task(void)
{
    if (Ini > Fin) return 1;
    if (Ini < MinG) Ini = MinG;
    if (Fin > MaxG) Fin = MaxG;
    Ini = (uint64_t)((Ini + Step - 2) / Step) * Step + 1;
    Fin = (uint64_t)((Fin - 1) / Step) * Step + 1;
    Cur = Ini;
    return 0;
}

static __inline__ int next_task(void)
{
    if (MaxG - Step >= Cur) Cur += Step;
    else return 6;
    if (Cur > Fin) return 7;
    return 0;
}

#define PBSTR "========================================================================"
#define PBWIDTH 45
#define SCRWIDTH 80
void do_progress( double percentage )
{
    int val = (int) (percentage);
    int lpad = (int) (percentage  * (val==100?SCRWIDTH:PBWIDTH) / 100);
    int rpad = (val==100?SCRWIDTH:PBWIDTH) - lpad;
    //fill progress bar with spaces
    fprintf(stderr, "\r%3d%% [%.*s%*s]", val, lpad, PBSTR, rpad, "");
    if (val!=100)
        fprintf(stderr, " (%" PRIu32 ",%" PRIu32 ",%" PRIu32 ",%" PRIu32 ",%" PRIu32 ",%" PRIu32 ")", pcCnt, ecCnt, fcCnt, ccCnt, icCnt, tcCnt);
    //fflush(stderr);
}

void print_factors(uint32_t i)
{
    uint64_t n = Block[i].Number;
    char FactorsStr[256], pclose[2], popen[2];
    if (Block[i].Div1Cnt == 1 && Factors[0][i].Power/2 == 1)
        fprintf(stderr, "%" PRIu64 " is prime\n",n);
    else
        if (Block[i].Div1Cnt > 1) fprintf(stderr, "%" PRIu64 " has %i different factors\n",n,Block[i].Div1Cnt);
        else fprintf(stderr, "%" PRIu64 " is a power of prime\n",n);
    bzero(FactorsStr, 256);
    if (Block[i].Div1Cnt > 1 || Factors[0][i].Power/2 > 1) {
        for (int j=0; j < Block[i].Div1Cnt; j++) {
            if (j > 0) sprintf(FactorsStr, "%s*", FactorsStr);
            sprintf(FactorsStr, "%s%" PRIu64, FactorsStr, Factors[j][i].Prime);
            if (Factors[j][i].Power/2 > 1) sprintf(FactorsStr, "%s^%i", FactorsStr, Factors[j][i].Power/2);
        }
        sprintf(FactorsStr, "%s = ", FactorsStr);
    }
    for (int j=0; j < Block[i].Div1Cnt; j++) {
        if (j > 0) sprintf(FactorsStr, "%s*", FactorsStr);
        if (Block[i].Div1Cnt > 1 || Factors[j][i].Power/2 > 1) {
            strcpy(popen, "(");
            strcpy(pclose, ")");
        }
        else {
            bzero(popen, 2);
            bzero(pclose, 2);
        }
        sprintf(FactorsStr, "%s%s%" PRIu64 "^2+%" PRIu64 "^2%s", FactorsStr, popen, Factors[j][i].A, Factors[j][i].B, pclose);
        if (Factors[j][i].Power/2 > 1) sprintf(FactorsStr, "%s^%i", FactorsStr, Factors[j][i].Power/2);
    }
    fprintf(stderr, "%" PRIu64 " = %s\n",n,FactorsStr);
    fprintf(stderr, "%" PRIu64 "^2 has %" PRId32 " different decompositions:\n",n,qSize);
    for (uint32_t j=0; j < qSize; j++)
        fprintf(stderr, "%" PRIu64 "^2 = %" PRIu64 "^2 + %" PRIu64 "^2\n", n, Q[j].A, Q[j].B);
    fprintf(stderr, "------------------------------------------------------------------------------\n");
}

void print_usage(void)
{
#ifdef _WIN32
	char pref[3] = "";
#elif __linux__ || unix || __unix__ || __unix
	char pref[3] = "./";
#endif // __linux__
    fprintf(stderr, "Usage: %spcuboid <low> <high> [switches]\n", pref);
    fprintf(stderr, "\t<low>\t\tlower border\n");
    fprintf(stderr, "\t<high>\t\thigher border\n");
    fprintf(stderr, "The following switches are accepted:\n");
    fprintf(stderr, "\t-a\t\tsearch for almost-perfect cuboids\n");
    fprintf(stderr, "\t-q\t\tsuppress output to stdout\n");
    fprintf(stderr, "\t-p\t\tdisplay progress bar\n");
    fprintf(stderr, "\t-o\t\twrite results to output file\n");
    fprintf(stderr, "\t-r\t\twrite task stat to report file\n");
    fprintf(stderr, "\t-s\t\tskip task if output file exists\n");
    fprintf(stderr, "\t-f [s]\t\tfactoring block size (default value: %" PRIu32 ")\n", block_size);
    fprintf(stderr, "\t-d [m]\t\tdebug mode\n\t\t\tdisplay (every [m]) factorization and decompositions\n");
    fprintf(stderr, "\t-v [n]\t\tverbose mode\n\t\t\tdisplay (every [n]) found results\n");
    fprintf(stderr, "\nCuboids in Real Numbers:\n");
    fprintf(stderr, "\t(P)erfect - cuboid with integer 3 edges, 3 face and 1 body diagonals\n");
    fprintf(stderr, "\t(E)dge - integer cuboid with only 1 irrational edge\n");
    fprintf(stderr, "\t(F)ace - integer cuboid with only 1 irrational face diagonal\n");
    fprintf(stderr, "\t(B)ody - integer cuboid with only 1 irrational body diagonal\n");
    fprintf(stderr, "Cuboids in Complex Numbers:\n");
    fprintf(stderr, "\t(C)omplex - Perfect cuboid in the space of complex numbers\n");
    fprintf(stderr, "\t(I)maginary - cuboid with complex edge and 1 irrational length\n");
    fprintf(stderr, "\t(T)wilight - cuboid with complex face diagonal and 1 irrational length\n");
    fprintf(stderr, "\t(M)idnight - cuboid with complex body diagonal and 1 irrational length\n");
}

int main(int argc, char** argv)
{
#if defined BOINC
	boinc_init();
#endif

#ifdef _WIN32
#elif __linux__ || unix || __unix__ || __unix
	char OS[256];
	struct utsname name;
	if(uname(&name)) exit(EXIT_FAILURE);
	sprintf(OS, "%s %s", name.sysname, name.release);
#endif // __linux__
    fprintf(stderr, "Perfect Cuboid %s (%s)\nCopyright 2017-2018, Alexander Belogourov aka x3mEn\n\n", VERSION, OS);
    if (argc < 3) {
        print_usage();
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    Task_Ini = Ini = string_to_u64(argv[1]);
    Task_Fin = Fin = string_to_u64(argv[2]);
    if (!Ini || !Fin) {
        print_usage();
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i],"-a")) {almost = 1; continue;}
        if (!strcmp(argv[i],"-q")) {quiet = 1; continue;}
        if (!strcmp(argv[i],"-p")) {progress = 1; continue;}
        if (!strcmp(argv[i],"-o")) {output = 1; continue;}
        if (!strcmp(argv[i],"-r")) {report = 1; continue;}
        if (!strcmp(argv[i],"-s")) {skip = 1; continue;}
        if (!strcmp(argv[i],"-f")) {continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-f")) {block_size = string_to_u64(argv[i]); continue;}
        if (!strcmp(argv[i],"-d")) {debug = 1; continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-d")) {debug_step = string_to_u64(argv[i]); continue;}
        if (!strcmp(argv[i],"-v")) {verbose = 1; continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-v")) {verbose_step = string_to_u64(argv[i]); continue;}
        print_usage();
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    ftime(&starttime);

    time_t timer;
    char curdatetime[26];
    struct tm* tm_info;
    time(&timer);
    tm_info = localtime(&timer);
    strftime(curdatetime, 26, "%d.%m.%Y %H:%M:%S", tm_info);

#ifndef BOINC
    sprintf(repfname, "rep_%019" PRIu64 "_%019" PRIu64, Task_Ini, Task_Fin);
    sprintf(outfname, "out_%019" PRIu64 "_%019" PRIu64, Task_Ini, Task_Fin);
    sprintf(chkfname, "chk_%019" PRIu64 "_%019" PRIu64, Task_Ini, Task_Fin);
#endif

    int ErrorCode, CheckPointCode;
    ErrorCode = CheckPointCode = read_checkpoint();
    if (ErrorCode) ErrorCode = init_task();
    if (ErrorCode) return ErrorCode;

    uint64_t total = Fin >= Ini ? (uint64_t)((Fin - Ini) / 4) + 1 : 0;

    sqrt2 = sqrtl(2);
    uint64_t step = 0, cubCnt = 0, block_elem = (block_size - 1) * 4;

    fout = fopen(outfname, "r");
    if (skip && fout != NULL && CheckPointCode) {
        fclose(fout);
#ifdef BOINC
	boinc_finish(EXIT_SUCCESS);
#endif
        exit (EXIT_SUCCESS);
    }
    if (output) {
        if (!CheckPointCode && fout == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
        if (CheckPointCode) {
            fout = fopen(outfname, "w");
        } else {
            fout = fopen(outfname, "a");
        }
        if (fout == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
    }

    fprintf(stderr, "Command line parameters :");
    for (int i = 1; i < argc; i++)
        fprintf(stderr, " %s", argv[i]);
    fprintf(stderr, "\n");
    fprintf(stderr, "Research Range borders  : from %" PRIu64 " to %" PRIu64 " step 4\n", Ini, Fin);
    fprintf(stderr, "Total amount of Numbers : %" PRIu64 "\n", total);
    fprintf(stderr, "Factoring Block Size    : %" PRIu32 "\n", block_size);
    fprintf(stderr, "Starting date timestamp : %s\n", curdatetime);
#ifdef BOINC
    fprintf(stderr, "\n");
#endif

    init_primes();

    if (progress) {
        fprintf(stderr, "%*s(P,E,F,C,I,T)\n",PBWIDTH+8,"");
    }

    int cpcnt, ctpcnt = 0;
    float cstep = 0.01;
    int fpcnt, ftpcnt = 0;
    float fstep = 0.0001;

    if (progress)
        do_progress(ctpcnt);
#ifdef BOINC
    boinc_fraction_done(0);
#endif

    while (Ini <= Cur && Cur <= Fin) {
        uint32_t bs = (Fin - Cur < block_elem ? Fin - Cur : block_elem) / 4 + 1;
        init_block(bs);
        factorize_range();
        decompose_factors();
        init_squares(double_powers());
        for (uint32_t i = 0; i < bSize; i++) {
            if (!(Block[i].Div3Cnt) && Block[i].Div1Cnt) {
                cnCnt++;
                find_all_squares(i);
                if (debug && !progress && !(cnCnt % debug_step))
                    print_factors(i);
                if (almost)
                    search_almost(Block[i].Number);
                else
                    search_perfect(Block[i].Number);
            }
            step = (Block[i].Number - Ini) / 4 + 1;
            cpcnt = (int)((double)step / total / cstep);
            if (ctpcnt != cpcnt || cubCnt < toCnt) {
                ctpcnt = cpcnt;
                cubCnt = toCnt;
                if (progress)
                    do_progress((double)step / total * 100);
                save_checkpoint(Block[i].Number + 1);
                if (output) fflush(fout);
                fflush(stdout);
            }
        }
        fpcnt = (int)((double)step / total / fstep);
        if (ftpcnt != fpcnt) {
            ftpcnt = fpcnt;
#ifdef BOINC
            boinc_fraction_done((double)step / total);
#endif
        }
        Cur += bSize * 4;
    };

    if (output) fclose(fout);
    remove(chkfname);

    ftime(&endtime);
    uint64_t dif = (endtime.time - starttime.time) * 1000 + (endtime.millitm - starttime.millitm);

#ifndef BOINC
    fprintf(stderr, "\n");
#endif
    fprintf(stderr, "Elapsed time            : %02d:%02d:%02d.%03d\n", (unsigned char)(dif/60/60/1000), (unsigned char)((dif/60/1000)%60), (unsigned char)((dif/1000)%60), (unsigned char)(dif%1000));
//    fprintf(stderr, "Loop cnt                : %" PRIu64 "\n", loopCnt);
//    fprintf(stderr, "Check sum               : %" PRIu64 "\n", check_sum);
    fprintf(stderr, "Candidates investigated : %" PRIu32 "\n", cnCnt);
    fprintf(stderr, "Perfect Cuboids found   : %" PRIu32 "\n", pcCnt);
    fprintf(stderr, "Edge Cuboids found      : %" PRIu32 "\n", ecCnt);
    fprintf(stderr, "Face Cuboids found      : %" PRIu32 "\n", fcCnt);
    fprintf(stderr, "Complex Cuboids found   : %" PRIu32 "\n", ccCnt);
    fprintf(stderr, "Imaginary Cuboids found : %" PRIu32 "\n", icCnt);
    fprintf(stderr, "Twilight Cuboids found  : %" PRIu32 "\n", tcCnt);
    if (report) {
        frep = fopen(repfname, "w");
        if(frep == NULL) {
            perror("Failed to open rep file");
#ifdef BOINC
			boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
        fprintf(frep,  "%" PRIu64
                      ",%" PRIu64
#ifdef BOINC
                      ",%" PRIu64
#endif
#ifndef BOINC
                      ",%s,%s,%02d:%02d:%02d.%03d"
#endif
                      ",%" PRIu64
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      "\n"
                    ,Task_Ini
                    ,Task_Fin
#ifdef BOINC
                    ,check_sum
#endif
#ifndef BOINC
                    ,VERSION
                    ,OS
                    ,(unsigned char)(dif/60/60/1000), (unsigned char)((dif/60/1000)%60), (unsigned char)((dif/1000)%60), (unsigned char)(dif%1000)
#endif
                    ,total
                    ,cnCnt
                    ,pcCnt
                    ,ecCnt
                    ,fcCnt
                    ,ccCnt
                    ,icCnt
                    ,tcCnt
               );
        fclose(frep);
    }
    free_squares();
    free_block();
    free_primes();
#ifdef BOINC
    boinc_finish(EXIT_SUCCESS);
#endif
    return (EXIT_SUCCESS);
}
/*
 * Раціональний кубоїд (або цілочисельна цеглина, або ідеальний кубоїд) — прямокутний паралелепіпед, у якого всі сім основних величин (три ребра, три лицьових діагоналі і просторова діагональ) є цілими числами, є однією з відкритих математичних проблем.
 * Інакше кажучи, раціональний кубоїд — цілочисельне рішення системи діофантових рівнянь.
 * a^2 + b^2 = d^2
 * a^2 + c^2 = e^2
 * b^2 + c^2 = f^2
 * a^2 + b^2 + c^2 = g^2
 * Досі невідомо, чи існує такий паралелепіпед. Комп'ютерний перебір не знайшов жодної цілочисельної цеглини з ребрами до 10^11.
 * Втім, знайдено кілька «майже цілочисельних» паралелепіпедів, у яких цілочисельними є всі величини, крім однієї:
 * (672, 153, 104) - одна з лицьових діагоналей не є цілим числом.
 * (520, 576, sqrt(618849)) - одне з ребер не є цілим числом.
 * У 2005 році тбіліський студент Лаша Маргішвілі запропонував доведення, що цілочисельний кубоід не існує — однак на 2009 рік робота так і не пройшла перевірку незалежними вченими.
 * Прямокутний паралелепіпед, у якого цілочисельні тільки ребра і лицьові діагоналі, називається ейлеровим.
 * Найменший з паралелепіпедів Ейлера — (240, 117, 44), з лицьовими діагоналями 267, 244 і 125.
 * Відомі такі вимоги до ейлерового паралелепіпеда (а значить, і до цілочисельної цеглини):
 * - Одне ребро ділиться на 4, друге ділиться на 16, третє непарне (якщо, звичайно, він примітивний — тобто, НСД (a, b, c) = 1).
 * - Одне ребро ділиться на 3 і ще одне — на 9.
 * - Одне ребро ділиться на 5.
 * - Одне ребро ділиться на 11.
 * - Одне ребро ділиться на 19.
 * - Одне ребро або просторова діагональ діляться на 13.
 * - Одне ребро, лицьова або просторова діагональ діляться на 17.
 * - Одне ребро, лицьова або просторова діагональ діляться на 29.
 * - Одне ребро, лицьова або просторова діагональ діляться на 37.
 * - Добуток ребер, лицьових і просторової діагоналі має ділитися на 2^8·3^4·5^3·7·11·13·17·19·29·37
 *
 *
 * Теорема 1.
 * Будь-яке непарне число, яке можна представити у вигляді суми квадратів двох цілих чисел при діленні на 4 дає залишок 1.
 * Доведення:
 * Із двох квадратів, сума яких непарна, обов'язково одне парне, а інше непарне.
 * Квадрат парного числа націло ділиться на 4, а квадрат непарного числа при діленні на 4 дає залишок 1.

 * Теорема 2.
 * Будь-яке просте число p, яке при ділені на 4 дає залишок 1, можна представити у вигляді суми квадратів двох натуральних чисел.
 * Доведення складається із двох лем:
 * Лема 1.
 * Для будь-якого простого числа p = 4k+1, де k - натуральне, існує таке целе число m, що m^2+1 = 0 (mod p).
 * Лема 2.
 * Будь-який простий дільник p числа m^2+1, де m - ціле, можна представити у вигляді суми квадратів двох натуральних чисел.

 * Із Теорем 1 та 2 випливає, що просте число p>2 не можна представити у вигляді суми лише двох квадратів, якщо воно має вигляд 4k+3, і має представлення, якщо p = 4k+1

 * Критерій Жирара.
 * Натуральне число можна представити у вигляді суми квадратів двох цілих чисел тоді і тільки тоді, коли в його розкладі на прості дільники усі прості дільники виду 4k+3 входятт із парними ступенями.
 *
 * Загальна формула для представлення добутку суми двох квадратів у вигляді суми двох квадратів наступна:
 * (a^2+b^2)(x^2+y^2) = a^2*x^2 + a^2*y^2 + b^2*x^2 + b^2*y^2,
 * додамо і віднімемо 2axby:
 * (a^2+b^2)(x^2+y^2) = a^2*x^2 + 2axby + b^2*y^2 + a^2*y^2 - 2axby + b^2*x^2 = (ax + by)^2 + (bx - ay)^2
 * Отже, (a^2+b^2)(x^2+y^2) = (ax + by)^2 + (bx - ay)^2 (1)
 *
 * а) Якщо число n є сумою двох квадратів, то і число 2n представляється у вигляді суми двох квадратів.
 * Доведення:
 * Якщо n = x^2 + y^2, то
 * (x+y)^2 + (x-y)^2 = x^2 + 2xy + y^2 + x^2 - 2xy + y^2 = 2x^2 + 2y^2 = 2(x^2+y^2) = 2n
 * Тобто
 * 2n = (x+y)^2 + (x-y)^2
 *
 * Теорема 3 (основна теорема арифметики):
 * Ціле число розкладається на прості множники одним єдиним способом (з точністю до перестановки множників і асоціативності)
 * Доведення цієї теореми залишимо за дужками.

 * Будь-яке число n можна представити у вигляді добутку простих чисел трьох типів: 2^a, p(i)^a(i), q(j)^b(j),
 * де p(i) - прості числа виду 4k+1, a(i) - ступінь числа p(i)
 * q(j) - прості числа виду 4k+3, b(j) - ступінь числа q(j).
 * Нехай Q = П q(j)^b(j)
 * Тоді, якщо Q не є повним квадратом (а це можливо лише тоді, коли всі b(j) парні), то n не можна розкласти на суму квадратів (критерій Жирара).
 * Якщо ж Q є повним квадратом, то кількість розкладів n дорівнює кількості розкладів числа П(p(i)^a(i)) на суми квадратів.
 *
 * Теорема 4 (формула Діріхле):
 * Якщо число n розкладається на суму квадратів, то кількість представлень дорівнює [ (П (a(i)+1)+1)/2 ] (2)
 * (Якщо кількість множників рівна 0, то добуток вважається рівним 1. Представлення, що відрізняються порядком доданків, не розрізняються)
 *
 * Основні висновки з цієї теореми:
 * 1) всі ступені простих 4k+3 мають бути парними, щоб n мало розклади
 * 2) кількість розкладів n залежить тільки від ступенів простих 4k+1
 * 3) наявність чи відсутність у розкладі двійки (2) у будь-яких ступенях не впливає ні на "розкладність" n, ні на кількість розкладів
 *
 * Із Теореми 4 і загальної формули (1) випливає, якщо n - парне і розкладається на суму квадратів m різними способами,
 * то і число n/2 розкладається на суми квадратів і до того ж теж m різними способами.
 * При цьому способи розкладу n/2 утворюються із розкладів n одним єдиним способом.
 * Отже, якщо число n має m розкладів на суму квадратів n = x(i)^2 + y(i)^2, то і число 2n має m розкладів, при цьому самі розклади утворюються одним єдиним способом:
 * 2n = (x+y)^2 + (x-y)^2
 *
 * Зазначимо, якщо число n має m розкладів на суму квадратів n = x(i)^2 + y(i)^2, то число 4n теж має m розладів, а самі розклади утворюються із розкладів числа n наступним чином:
 * 4n = 2^2 * n = (2x)^2 + (2y)^2
 *
 * Повернемося до системи діафантових рівнянь.
 * a^2 + b^2 = d^2
 * a^2 + c^2 = e^2
 * b^2 + c^2 = f^2
 * a^2 + f^2 = g^2
 *
 * Ребра a, b, c мають бути різні (інакше лицьова діагональ між двома рівними ребрами довжини x буде іраціональним числом x*sqrt(2)), тому
 * для g^2 має існувати як мінімум 3 різні розклади на суми квадратів:
 * g^2 = a^2 + f^2
 * g^2 = b^2 + e^2
 * g^2 = c^2 + d^2
 *
 * Для того, щоб n = g^2 розкладалося на суму квадратів, потрібно, щоб у розкладі n прості числа 4k+3 були представлені у парних ступенях.
 * До того ж n має бути повним квадратом, а це можливо тоді і тільки тоді, коли всі прості множники n представлені у парних ступенях.
 *
 * Тепер доведемо, що діагональ мінімального ідеального кубоїда є непарним числом.
 * По-перше зазначимо, якщо ідеальний кубоїд існує, значить їх існує нескінченно багато.
 * Адже лінійно збільшуючи "габарити" кубоїда ми отримаємо так само ідеальний кубоїд.
 * Тому задача полягає в пошуку нетривіального ідеального кубоїда мінімального розміру.
 *
 * Припустимо, що просторова діагональ g є числом парним.
 * Тоді, як доведено вище, має розклад на суму квадратів і число (g/2)^2.
 * І нам відомо, яким саме єдиним чином:
 * (g/2)^2 = (a/2)^2 + (f/2)^2
 * (g/2)^2 = (b/2)^2 + (e/2)^2
 * (g/2)^2 = (c/2)^2 + (d/2)^2
 * З парності g випливає парність a, b, c, d, e, f
 * Отже кубоїд з парною просторовою діагоналлю g не є мінімальним.
 * Висновок: у нетривіального ідеального кубоїд просторова діагональ g має бути числом непарним.
 *
 * Теорема 5.
 * Якщо просте число p не можна представити у вигляді суми двох квадратів, і якщо сума квадратів x^2+y^2 кратна p, то кожне із цілих чисел x, y кратне p.
 * Доведення цієї теореми наведено в http://kvant.mccme.ru/pdf/1999/03/kv0399senderov.pdf на сторінці 20.
 *
 * Із Теорем 1 і 5 випливає, що якщо в розкладі просторовою діагоналі g є прості числа виду 4k+3 у будь-яких ступенях, то і всі a, b, c, d, e, f кратні всім цим 4k+3, оскільки прості числа виду 4k+3 не розкладаються на суму лише двох квадратів,
 * а значить кубоїд не є мінімальним, оскільки всю систему рівнянь можна спростити, поділивши всі рівняння на число Q = П q(j)^b(j), де q(j) - попарно різні прості числа виду 4k+3, b(j) - ступені q(j).
 *
 * Таким чином якщо нетривіальний ідеальний кубоїд існує, його просторова діагональ має мати вигляд добутку простих чисел виду 4k+1:
 * g = П (p(i)^a(i))
 *
 **********************************************************************************************************
 *
 * Програма веде пошук просторової діагоналі у заданому наперед діапазоні [Ini, Fin] серед чисел виду 4k+1,
 * що можна представити у вигляді добутку лише простих виду 4k+1.
 * Усі інші числа відкидаються одразу як визначається, що число N містить простий дільник 4k+3.
 *
 * Факторизація діапазону чисел відбувається методом відсіву через решето простих від 3 до квадратного кореня з максимального числа діапазону.
 * Надалі розглядаються лише кандидати, що мають лише прості дільники виду 4k+1, а також самі по собі не є простими числами.
 *
 * Після факторизації виконується декомпозиція кожного простого фактору виду 4k+1 на суму двох квадратів.
 *
 * Після декомпозиції виконується комбінаторна декомпозиція N на суми двох квадратів.
 */
