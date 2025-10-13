#include <stdint.h>
#include <stdbool.h>
#include <iostream>
#include <vector>

uint64_t ModPrime(uint64_t og, int irange, int erange);
uint64_t MidPrime(uint64_t og, int irange, int erange);
uint64_t MaxPrime(uint64_t og, int irange, int erange);
uint64_t TheoreticalMaxPrime(uint64_t og, int irange, int erange);
bool is_prime(uint64_t n);
using namespace std;

int counter = 0;
int tested_counter = 0;

uint64_t Poffset(uint64_t no, bool& found_prime)
{
    uint64_t use = no;
    uint64_t list[23] = { 1,5,11,13,17,19,23,25,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89 };
    vector<uint64_t> usable;
    int limit = 18;
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
          if (i == 17 && limit < 23) limit = 23;
    }
    cout << "Composite: " << (use + usable[0]) << endl;
    found_prime = false;  
    return use + usable[0];
}

// FIXED: Same fix for negative offset
uint64_t Noffset(uint64_t no, bool& found_prime)
{
    uint64_t use = no;
    uint64_t list[23] = { 1,5,11,13,17,19,23,25,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89 };
    vector<uint64_t> usable;
    int limit = 18;
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
          if (i == 17 && limit < 23) limit = 23;
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
int main() {
    int choice;
    uint64_t start, end;

    while (true) {
        cout << "\n=== PRIME GENERATOR ===" << endl;
        cout << "1. ModPrime (6k ± 13)" << endl;
        cout << "2. MidPrime (60k ± 1)" << endl;
        cout << "3. MaxPrime (42k ± {11,13})" << endl;
        cout << "4. TheoreticalMax (Dynamic 20-offset)" << endl;
        cout << "5. Exit" << endl;
        cout << "Choose method: ";
        cin >> choice;

        if (choice == 5) break;
        if (choice < 1 || choice > 4) {
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
        }

        cout << "\nPress Enter to continue...";
        cin.ignore();
        cin.get();
    }

    return 0;
}
