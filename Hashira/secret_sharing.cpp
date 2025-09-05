#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <cmath>
#include <algorithm>
#include <boost/multiprecision/cpp_int.hpp>
#include "include/json.hpp"

using json = nlohmann::json;
using boost::multiprecision::cpp_int;

// Class for big integers using boost::multiprecision
class BigInt {
private:
    cpp_int value;

public:
    BigInt() : value(0) {}

    BigInt(int val) : value(val) {}

    BigInt(const std::string& str, int base = 10) {
        // Parse string according to base
        value = 0;
        cpp_int multiplier = 1;
        for (int i = str.length() - 1; i >= 0; i--) {
            int digit;
            if (str[i] >= '0' && str[i] <= '9') {
                digit = str[i] - '0';
            } else if (str[i] >= 'a' && str[i] <= 'z') {
                digit = str[i] - 'a' + 10;
            } else if (str[i] >= 'A' && str[i] <= 'Z') {
                digit = str[i] - 'A' + 10;
            } else {
                continue; // Skip non-digit characters
            }
            
            if (digit >= base) {
                throw std::invalid_argument("Digit out of range for given base");
            }
            
            value += cpp_int(digit) * multiplier;
            multiplier *= base;
        }
    }

    BigInt(const BigInt& other) : value(other.value) {}

    BigInt& operator=(const BigInt& other) {
        if (this != &other) {
            value = other.value;
        }
        return *this;
    }

    BigInt operator+(const BigInt& other) const {
        BigInt result;
        result.value = value + other.value;
        return result;
    }

    BigInt operator-(const BigInt& other) const {
        BigInt result;
        result.value = value - other.value;
        return result;
    }

    BigInt operator*(const BigInt& other) const {
        BigInt result;
        result.value = value * other.value;
        return result;
    }

    BigInt operator/(const BigInt& other) const {
        BigInt result;
        result.value = value / other.value;
        return result;
    }

    BigInt operator%(const BigInt& other) const {
        BigInt result;
        result.value = value % other.value;
        return result;
    }

    bool operator==(const BigInt& other) const {
        return value == other.value;
    }

    bool operator!=(const BigInt& other) const {
        return value != other.value;
    }

    bool operator<(const BigInt& other) const {
        return value < other.value;
    }

    bool operator<=(const BigInt& other) const {
        return value <= other.value;
    }

    bool operator>(const BigInt& other) const {
        return value > other.value;
    }

    bool operator>=(const BigInt& other) const {
        return value >= other.value;
    }

    std::string toString() const {
        return value.str();
    }

    friend std::ostream& operator<<(std::ostream& os, const BigInt& num) {
        os << num.toString();
        return os;
    }
};

// Converts a string value from a given base to BigInt
BigInt baseToDecimal(const std::string& value, int base) {
    return BigInt(value, base);
}

// A large predefined prime to use for Shamir's Secret Sharing
// This is a 256-bit prime number which is more than enough for our needs
const BigInt LARGE_PRIME("115792089237316195423570985008687907853269984665640564039457584007913129639747");

// Extended Euclidean Algorithm for modular inverse
BigInt modInverse(const BigInt& a, const BigInt& m) {
    BigInt m0 = m;
    BigInt y(0);
    BigInt x(1);
    BigInt a_mod = a % m;

    if (a_mod < BigInt(0))
        a_mod = a_mod + m;

    while (a_mod > BigInt(1)) {
        BigInt q = a_mod / m;
        BigInt t = m;

        m = a_mod % m;
        a_mod = t;
        
        t = y;
        y = x - (q * y);
        x = t;
    }

    if (x < BigInt(0))
        x = x + m0;

    return x;
}

// Evaluate polynomial at x (mod prime) using Horner's method
BigInt evalPoly(const std::vector<BigInt>& coeffs, const BigInt& x, const BigInt& prime) {
    BigInt result(0);
    for (int i = coeffs.size() - 1; i >= 0; i--) {
        result = (result * x + coeffs[i]) % prime;
    }
    return result;
}

// Optimized polynomial multiplication that only computes terms up to degree limit
std::vector<BigInt> polyMulLimited(
    const std::vector<BigInt>& a, 
    const std::vector<BigInt>& b, 
    int limit, 
    const BigInt& prime) {
    
    std::vector<BigInt> res(limit + 1, BigInt(0));
    
    for (int i = 0; i < a.size() && i <= limit; i++) {
        for (int j = 0; j < b.size() && i + j <= limit; j++) {
            res[i + j] = (res[i + j] + (a[i] * b[j]) % prime) % prime;
        }
    }
    
    return res;
}

// Reconstructs the full polynomial coefficients using Lagrange interpolation (optimized)
std::vector<BigInt> lagrangeCoefficients(
    const std::vector<std::pair<BigInt, BigInt>>& points, 
    const BigInt& prime) {
    
    int k = points.size();
    std::vector<BigInt> coeffs(k, BigInt(0));

    // Precompute denominators
    std::vector<BigInt> denoms(k, BigInt(1));
    
    for (int i = 0; i < k; i++) {
        BigInt xi = points[i].first;
        for (int j = 0; j < k; j++) {
            if (i != j) {
                denoms[i] = (denoms[i] * (xi - points[j].first)) % prime;
            }
        }
        denoms[i] = modInverse(denoms[i], prime);
    }

    for (int i = 0; i < k; i++) {
        BigInt yi = points[i].second;

        // Compute the basis polynomial for this point
        std::vector<BigInt> basis(k, BigInt(0));
        basis[0] = BigInt(1);
        int deg = 0;

        for (int j = 0; j < k; j++) {
            if (i != j) {
                BigInt xj = points[j].first;
                std::vector<BigInt> term = {BigInt(0) - xj, BigInt(1)};  // -xj + 1*x
                basis = polyMulLimited(basis, term, deg + 1, prime);
                deg++;
            }
        }

        // Scale by yi * inverse of denominator
        BigInt scale = (yi * denoms[i]) % prime;
        for (int d = 0; d <= deg; d++) {
            basis[d] = (basis[d] * scale) % prime;
        }

        // Add to coefficients
        for (int d = 0; d <= deg; d++) {
            coeffs[d] = (coeffs[d] + basis[d]) % prime;
        }
    }

    return coeffs;
}

// Lagrange interpolation at x=0 to find the secret (optimized)
BigInt lagrangeInterpolation(const std::vector<std::pair<BigInt, BigInt>>& points, const BigInt& prime) {
    BigInt secret(0);
    int k = points.size();

    // Precompute the denominators for efficiency
    std::vector<BigInt> denoms(k, BigInt(1));
    for (int i = 0; i < k; i++) {
        BigInt xi = points[i].first;
        for (int j = 0; j < k; j++) {
            if (i != j) {
                denoms[i] = (denoms[i] * (xi - points[j].first)) % prime;
            }
        }
        denoms[i] = modInverse(denoms[i], prime);
    }

    // Compute the secret using the optimized approach
    for (int i = 0; i < k; i++) {
        BigInt yi = points[i].second;
        BigInt lagrange = denoms[i];
        for (int j = 0; j < k; j++) {
            if (i != j) {
                lagrange = (lagrange * (BigInt(0) - points[j].first)) % prime;
            }
        }
        secret = (secret + (yi * lagrange) % prime) % prime;
    }
    
    return (secret + prime) % prime;
}

// Check if a number is prime
bool isPrime(const BigInt& x) {
    if (x < BigInt(2)) return false;
    if (x == BigInt(2)) return true;
    if (x % BigInt(2) == BigInt(0)) return false;
    
    BigInt i(3);
    BigInt limit = x;
    mpz_sqrt(limit.get_mpz_t(), x.get_mpz_t());
    
    while (i <= limit) {
        if (x % i == BigInt(0)) return false;
        i = i + BigInt(2);
    }
    
    return true;
}

// Returns the next prime greater than or equal to n
BigInt nextPrime(BigInt n) {
    while (!isPrime(n)) {
        n = n + BigInt(1);
    }
    return n;
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cout << "Usage: " << argv[0] << " <input.json>" << std::endl;
        return 1;
    }

    // Read the JSON file
    std::ifstream file(argv[1]);
    if (!file.is_open()) {
        std::cerr << "Failed to open file: " << argv[1] << std::endl;
        return 1;
    }

    json data;
    try {
        file >> data;
    } catch (const json::exception& e) {
        std::cerr << "JSON parsing error: " << e.what() << std::endl;
        return 1;
    }

    int k = data["keys"]["k"];

    // Collect all shares
    std::vector<std::pair<BigInt, BigInt>> allPoints;
    for (auto& [key, value] : data.items()) {
        if (key == "keys") continue;
        
        int shareIndex = std::stoi(key);
        int base = std::stoi(value["base"].get<std::string>());
        std::string shareValue = value["value"];
        
        BigInt decimalValue = baseToDecimal(shareValue, base);
        allPoints.push_back({BigInt(shareIndex), decimalValue});
    }

    if (allPoints.size() < k) {
        std::cout << "Not enough shares to reconstruct the secret." << std::endl;
        return 1;
    }

    // Use the first k shares to reconstruct the secret
    std::vector<std::pair<BigInt, BigInt>> points(allPoints.begin(), allPoints.begin() + k);

    // Use the predefined large prime
    BigInt prime = LARGE_PRIME;

    std::cout << "Reconstructing secret..." << std::endl;
    BigInt secret = lagrangeInterpolation(points, prime);
    std::cout << "Recovered secret: " << secret << std::endl;

    // Check for wrong shares
    std::cout << "Checking for wrong shares..." << std::endl;
    std::vector<std::pair<BigInt, BigInt>> wrongShares;

    // Optimize by computing polynomial coefficients once
    std::vector<BigInt> coeffs = lagrangeCoefficients(points, prime);

    for (const auto& pt : allPoints) {
        BigInt x = pt.first;
        BigInt y = pt.second;
        BigInt fx = evalPoly(coeffs, x, prime);
        if (fx != y) {
            wrongShares.push_back(pt);
        }
    }

    if (!wrongShares.empty()) {
        std::cout << "Wrong shares detected:" << std::endl;
        for (const auto& pt : wrongShares) {
            std::cout << "Share x=" << pt.first << ", value=" << pt.second << std::endl;
        }
    } else {
        std::cout << "No wrong shares detected." << std::endl;
    }

    return 0;
}
