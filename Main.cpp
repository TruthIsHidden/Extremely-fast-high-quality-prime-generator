#include <stdint.h>
#include <stdbool.h>
#include <vector>
#include <fstream>
#include <algorithm>
#include <unordered_set>
#include <iostream>
#include <string>
#include <bitset>
#include <random>
#include <iomanip>
#include <sstream>
#include <cctype>
#include <unordered_map>
#include <chrono>
#include <limits>
#include <cstdint>
#include <locale>
#include <map>
#include <set>

uint64_t ModPrime(uint64_t og, int irange, int erange);
uint64_t MidPrime(uint64_t og, int irange, int erange);
uint64_t MaxPrime(uint64_t og, int irange, int erange);
uint64_t TheoreticalMaxPrime(uint64_t og, int irange, int erange);
uint64_t PRNG(uint64_t value);
bool is_prime(uint64_t n);
using namespace std;

uint64_t list[25] = {
  1, 11, 13, 17, 19,
  23, 29, 31, 37, 41,
  43, 47, 53, 59, 61,
  67, 71, 73, 79, 83,
  89, 97, 101, 103, 107
};
typedef uint64_t u64;
typedef unsigned __int128 u128; 

uint64_t KEY = 0;
static inline u64 prng64_from(u64 &state) {
    state = PRNG(state);
    return state;
}

uint64_t gcd_u64(uint64_t a, uint64_t b) {
    while (b != 0) {
        uint64_t t = b;
        b = a % b;
        a = t;
    }
    return a;
}

static inline u64 derive_working_key(u64 key, u64 i, u64 irange, u64 erange) {
    u64 x = key ^ 0x9E3779B97F4A7C15ULL ^ (i - irange) ^ ((erange - i) << 1);
    x = PRNG(x);
    x = PRNG(x);
    return x ? x : 0xA5A5A5A5A5A5A5A5ULL; 
}


uint64_t rotate_left_64(uint64_t value, unsigned int positions) {
	positions %= 64;
	return (value << positions) | (value >> (64 - positions));
}

uint64_t rotate_right_64(uint64_t value, unsigned int positions) {
	positions %= 64;
	return (value >> positions) | (value << (64 - positions));
}

uint8_t rotate_left(uint8_t byte, unsigned int i) {
	i %= 8;
	return (byte << i) | (byte >> (8 - i));
}

uint8_t rotate_right(uint8_t byte, unsigned int i) {
	i %= 8;
	return (byte >> i) | (byte << (8 - i));
}

uint64_t PRNG(uint64_t value)
{
    uint64_t og = value;
    const uint64_t Tera = 5846788331219253894ULL;
    const uint64_t Tera_A = 14334443016395714402ULL;
    const uint64_t e = 57139ULL;
    const uint64_t pi_scaled = 314159ULL;
    const uint64_t GRC = 0x9E3779B97F4A7C15ULL;
    uint64_t salt = og ^ Tera;
    value ^= GRC;
    value ^= value >> 32;
    value ^= rotate_left_64(value, 31);
    value *= 0xD2B74407B1CE6E93ULL;
    value ^= rotate_left_64(value, 29);
    value = 2 * value + 13;

    for (int i = 0;i < 8;i++)
    {
        value ^= salt;
        uint8_t byte1 = (value >> 0) & 0xFF; //
        uint8_t byte2 = (value >> 8) & 0xFF;//
        uint8_t byte3 = (value >> 16) & 0xFF;//
        uint8_t byte4 = (value >> 24) & 0xFF;//
        uint8_t byte5 = (value >> 32) & 0xFF;//
        uint8_t byte6 = (value >> 40) & 0xFF;//
        uint8_t byte7 = (value >> 48) & 0xFF;//
        uint8_t byte8 = (value >> 56) & 0xFF;//
        byte1 *= (Tera + Tera_A) ^ (e + GRC);
        byte1 += ~i;
        byte1 ^= rotate_left(e + (uint8_t)pi_scaled ^ ~byte4, 3) ^ ~(byte7 << 3);
        byte8 ^= rotate_right(i ^ (uint8_t)Tera_A + byte1, 3) ^ (byte6 << 3);
        byte4 ^= rotate_left(~byte3 + byte6 ^ (uint8_t)Tera_A, 3) ^ (byte8 << 3) ^ (uint8_t)og;
        byte7 ^= rotate_right(byte7 - byte4 ^ (uint8_t)e, 3);
        byte5 ^= byte2;
        byte2 ^= rotate_right(Tera_A ^ i, 7);
        byte6 ^= (byte3 << 3) ^ byte5;
        byte3 ^= rotate_left(byte2 ^ ((uint8_t)og * ~byte2), 3);
        byte1 += byte8;
        byte2 += byte7;
        byte3 += byte6;
        byte4 += byte5;
        byte8 ^= byte7;
        byte7 ^= byte6;
        byte6 ^= byte5;
        byte5 ^= byte4;
        value = ((uint64_t)byte1 << 0)   // position 0
            | ((uint64_t)byte8 << 8)     // position 1
            | ((uint64_t)byte2 << 16)    // position 2
            | ((uint64_t)byte7 << 24)    // position 3
            | ((uint64_t)byte3 << 32)    // position 4
            | ((uint64_t)byte6 << 40)    // position 5
            | ((uint64_t)byte4 << 48)    // position 6
            | ((uint64_t)byte5 << 56);
        value ^= rotate_right_64(GRC ^ (uint64_t)i + (uint64_t)byte3 ^ (uint64_t)byte6 ^ ~(uint64_t)byte1, 33) * ~((uint64_t)byte4 ^ Tera);
        salt ^= rotate_left_64((uint64_t)byte5 ^ (uint64_t)byte3, 33) ^ (~value << 13) ^ ((19 - i) + ~i ^ byte6);
        value ^= og;
        value ^= value << 13;
    }
    return value;
}

static inline u64 sample_k_wrapped_seeded(u64 K, u64 keyseed) {
    if (K == 0) return 0;
    __uint128_t L = ( __uint128_t)K >> 1;
    __uint128_t H = ( __uint128_t)K + ( (__uint128_t)K >> 1);
    __uint128_t span = H - L + 1;

    const __uint128_t U = ( (__uint128_t)std::numeric_limits<u64>::max() + 1);
    __uint128_t t = (U / span) * span;

    u64 state = PRNG(keyseed);
    u64 r;
    do { state = PRNG(state); r = state; } while ( (__uint128_t)r >= t );

    __uint128_t center = ( __uint128_t)K - L; // 0..span-1
    __uint128_t off = (center + ( (__uint128_t)r % span)) % span;
    return (u64)(L + off);
}


int counter = 0;
int tested_counter = 0;

uint64_t Poffset(uint64_t no, bool& found_prime)
{
    uint64_t use = no;
    vector<uint64_t> usable;
    int limit = 25;
    for (int i = 0; i < limit; i++)
    {
        if ((use + list[i]) % 7 != 0)
        {
            usable.push_back(list[i]);
            if (is_prime(use + list[i]))
            {
                cout << "Prime: " << (use + list[i]) << endl;
                found_prime = true;  
                return (use + list[i]);
            }
        }
    }
    cout << "Composite: " << (use + usable[0]) << endl;
    found_prime = false;  
    return use + usable[0];
}

uint64_t Noffset(uint64_t no, bool& found_prime)
{
    uint64_t use = no;
    vector<uint64_t> usable;
    int limit = 25;
    for (int i = 0; i < limit; i++)
    {
        if ((use - list[i]) % 7 != 0)
        {
            usable.push_back(list[i]);
            if (is_prime(use - list[i]))
            {
                cout << "Prime: " << (use - list[i]) << endl;
                found_prime = true; 
                return (use - list[i]);
            }
        }
    }
    cout << "Composite: " << (use - usable[0]) << endl;
    found_prime = false; 
    return use - usable[0];
}
/*bool is_prime(uint64_t n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;

    // Check divisibility by numbers of form 6k±1
    for (uint64_t i = 5; i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0)
            return false;
    }
    return true;
}*/
uint64_t mod_mul(uint64_t a, uint64_t b, uint64_t mod) {
    uint64_t result = 0;
    a %= mod;
    while (b > 0) {
        if (b & 1) {
            result = (result + a) % mod;
        }
        a = (a * 2) % mod;
        b >>= 1;
    }
    return result;
}

// Modular exponentiation: (base^exp) % mod
uint64_t mod_pow(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) {
            result = mod_mul(result, base, mod);
        }
        base = mod_mul(base, base, mod);
        exp >>= 1;
    }
    return result;
}

bool miller_rabin(uint64_t n, int rounds = 40) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0) return false;

    uint64_t d = n - 1;
    int r = 0;
    while (d % 2 == 0) {
        d /= 2;
        r++;
    }

    uint64_t witnesses[] = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 };
    int num_witnesses = (rounds < 12) ? rounds : 12;

    for (int i = 0; i < num_witnesses; i++) {
        uint64_t a = witnesses[i];
        if (a >= n) continue;

        uint64_t x = mod_pow(a, d, n);
        if (x == 1 || x == n - 1) continue;

        bool composite = true;
        for (int j = 0; j < r - 1; j++) {
            x = mod_mul(x, x, n);
            if (x == n - 1) {
                composite = false;
                break;
            }
        }
        if (composite) return false;
    }
    return true;
}

bool is_prime(uint64_t n) {
    return miller_rabin(n, 40);
}

uint64_t Compute(uint64_t n) {
    static const uint32_t S[] = {
         2,  3,  5,  7, 11, 13, 17, 19, 23, 29,
    31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97,101,103,107,109,113,
   127,131,137,139,149,151,157,163,167,173,
   179,181,191,193,197,199,211,223,227,229,
   233,239,241,251,257,263,269,271,277,281,
   283,293,307,311,313,317,331,337,347,349,
   353,359,367,373,379,383,389,397,401,409,
   419,421,431,433,439,443,449,457,461,463,
   467,479,487,491,499
    };
    constexpr size_t P = sizeof(S)/sizeof(S[0]);

    uint32_t b[P], rem[P];
    for (size_t i = 0; i < P; ++i) {
        uint32_t p = S[i];
        b[i] = (p - (uint32_t)(n % p)) % p;
        rem[i] = 0;                        
    }

    for (uint64_t t = 0;; ++t) {
        bool ok = true;
        for (size_t i = 0; i < P; ++i) {
            if (rem[i] == b[i]) { ok = false; break; }
        }
        if (ok) return n + t;
        for (size_t i = 0; i < P; ++i) {
            uint32_t p = S[i];
            uint32_t r = rem[i] + 1;
            rem[i] = (r == p ? 0 : r);
        }
    }
}
uint64_t ModPrime(uint64_t og, uint64_t irange, uint64_t erange)
{
    int no = 0;
    int pos, neg;
    for (int i = irange;i < erange;i++)
    {
        pos = 6 * i + 13;
        neg = 6 * i - 13;
        if (is_prime(pos))
        {
            cout << "Prime: " << pos << endl;
            no++;
        }
        else cout << "Composite: " << pos << endl;
        if (is_prime(neg))
        {
            cout << "Prime: " << neg << endl;
            no++;
        }
        else cout << "Composite: " << neg << endl;
    }
    return no;
}
uint64_t MidPrime(uint64_t og, uint64_t irange, uint64_t erange)
{
    int no = 0;
    int pos, neg;
    for (int i = irange;i < erange;i++)
    {
        uint64_t main = 60 * i;
        pos = main + 1;
        neg = main - 1;
        if (is_prime(pos))
        {
            cout << "Prime: " << pos << endl;
            no++;
        }
        else cout << "Composite: " << pos << endl;
        if (is_prime(neg))
        {
            cout << "Prime: " << neg << endl;
            no++;
        }
        else cout << "Composite: " << neg << endl;
    }
    return no;
    return 0;

}
uint64_t TheoreticalMaxPrime(uint64_t og, uint64_t irange, uint64_t erange)
{
    int primes_found = 0;
    int total_attempts = 0;

    for (uint64_t i = irange; i < erange; i++)
    {
        uint64_t main = 30 * i;
        bool pos_is_prime = false;
        bool neg_is_prime = false;

        uint64_t pos = Poffset(main, pos_is_prime);
        uint64_t neg = Noffset(main, neg_is_prime);

        if (pos_is_prime) primes_found++;
        if (neg_is_prime) primes_found++;
        total_attempts += 2;
    }

    cout << "\nPrimes found: " << primes_found << "/" << total_attempts;
    if (total_attempts > 0) {
        cout << " (" << (double)(primes_found * 100) / (double)total_attempts << "%)" << endl;
    }

    return primes_found;
}

uint64_t TheoreticalMaxPrimeS(uint64_t og, uint64_t irange, uint64_t erange)
{
    int primes_found = 0;
    int total_attempts = 0;
    uint64_t seed = 0;
    uint64_t workingKEY = 0;
    for (uint64_t i = irange; i < erange; i++)
    {
        workingKEY = derive_working_key(KEY, i, irange, erange);
        u64 k = sample_k_wrapped_seeded(i,workingKEY);
        u128 base128 = (u128)30 * (u128)k;                  
        u64 main = (u64)(base128 % std::numeric_limits<u64>::max());              
        bool pos_is_prime = false;
        bool neg_is_prime = false;

        uint64_t pos = Poffset(main, pos_is_prime);
        uint64_t neg = Noffset(main, neg_is_prime);

        if (pos_is_prime) primes_found++;
        if (neg_is_prime) primes_found++;
        total_attempts += 2;
    }
    cout << "\nPrimes found: " << primes_found << "/" << total_attempts;
    if (total_attempts > 0) {
        cout << " (" << (double)(primes_found * 100) / (double)total_attempts << "%)" << endl;
    }
    return (uint64_t)primes_found;
}
uint64_t MaxPrime(uint64_t og, uint64_t irange, uint64_t erange)
{
    int no = 0;
    int pos, neg;
    for (int i = irange;i < erange;i++)
    {
        uint64_t main = 42 * i;
        pos = ((main + 13) % 5 == 0) ? main + 11 : main + 13;
        neg = ((main - 13) % 5 == 0) ? main - 11 : main - 13;
        if (is_prime(pos))
        {
            cout << "Prime: " << pos << endl;
            no++;
        }
        else cout << "Composite: " << pos << endl;
        if (is_prime(neg))
        {
            cout << "Prime: " << neg << endl;
            no++;
        }
        else cout << "Composite: " << neg << endl;
    }
    return no;
}

uint64_t NewConceptMax(uint64_t irange, uint64_t erange) {
    uint64_t counter = 0;
    uint64_t n = irange;

    while (n < erange) {
        uint64_t candidate = Compute(n);

        if (is_prime(candidate)) {
            cout << "Prime: " << candidate << endl;
            counter++;
        } else {
            cout << "Composite: " << candidate << endl;
        }
        n = candidate + 1;
    }

    return counter;
}
int main() {
    int choice;
    uint64_t start, end;

    while (true) {
        cout << "\n=== PRIME GENERATOR ===" << endl;
        cout << "1. ModPrime (6k ± 13)" << endl;
        cout << "2. MidPrime (60k ± 1)" << endl;
        cout << "3. MaxPrime (42k ± {11,13})" << endl;
        cout << "4. TheoreticalMax (Dynamic 20-offset)" << endl;
        cout << "5. TheoreticalMax, ONEWAY-VARIANT" << endl;
        cout << "6. New CoPrime Approach" << endl;
        cout << "7. Exit" << endl;
        cout << "Choose method: ";
        cin >> choice;

        if (choice == 7) break;
        if (choice < 1 || choice > 6) {
            cout << "Invalid choice!" << endl;
            continue;
        }

        cout << "Enter start k: ";
        cin >> start;
        cout << "Enter end k: ";
        cin >> end;

        uint64_t primes_found, total_tested;

        switch (choice) {
        case 1:
            primes_found = ModPrime(0, start, end);
            total_tested = 2 * (end - start);
            cout << "Primes: " << primes_found << "/" << total_tested;
            cout << " (" << (primes_found * 100) / total_tested << "%)" << endl;
            break;

        case 2:
            primes_found = MidPrime(0, start, end);
            total_tested = 2 * (end - start);
            cout << "Primes: " << primes_found << "/" << total_tested;
            cout << " (" << (primes_found * 100) / total_tested << "%)" << endl;
            break;

        case 3:
            primes_found = MaxPrime(0, start, end);
            total_tested = 2 * (end - start);
            cout << "Primes: " << (double)primes_found << "/" << (double)total_tested;
            cout << " (" << (double)(primes_found * 100) / total_tested << "%)" << endl;
            break;

        case 4:
            counter = 0;
            tested_counter = 0;
            primes_found = TheoreticalMaxPrime(0, start, end);
            
            break;
        
        case 5:
        counter = 0;
        tested_counter = 0;
        cout << "Key: ";
        cin >> KEY;
        primes_found = TheoreticalMaxPrimeS(0, start, end);
        break;
        
        case 6: 
    counter = 0;
    tested_counter = 0;

    uint64_t primes_found = NewConceptMax(start, end);
    uint64_t total_tested = (end > start) ? (end - start) : 0;

    if (total_tested == 0) {
        cout << "No tests (start >= end)\n";
    } else {
        cout << "Primes: " << primes_found << "/" << total_tested
             << " (" << fixed << setprecision(2)
             << (100.0 * primes_found / total_tested) << "%)\n";
    }
    break;
        }

        cout << "\nPress Enter to continue...";
        cin.ignore();
        cin.get();
    }

    return 0;
}
