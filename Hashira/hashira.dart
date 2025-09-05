import 'dart:convert';
import 'dart:io';

// Converts a string value from a given base to BigInt
BigInt baseToDecimal(String value, int base) {
  return BigInt.parse(value, radix: base);
}

// A large predefined prime to use for Shamir's Secret Sharing
// This is a 256-bit prime number which is more than enough for our needs
final BigInt LARGE_PRIME = BigInt.parse(
    "115792089237316195423570985008687907853269984665640564039457584007913129639747");

// Lagrange interpolation at x=0 to find the secret (optimized)
BigInt lagrangeInterpolation(List<List<BigInt>> points, BigInt prime) {
  BigInt secret = BigInt.zero;
  int k = points.length;

  // Precompute the denominators for efficiency
  List<BigInt> denoms = List.filled(k, BigInt.one);
  for (int i = 0; i < k; i++) {
    BigInt xi = points[i][0];
    for (int j = 0; j < k; j++) {
      if (i != j) {
        denoms[i] = (denoms[i] * (xi - points[j][0])) % prime;
      }
    }
    denoms[i] = modInverse(denoms[i], prime);
  }

  // Compute the secret using the optimized approach
  for (int i = 0; i < k; i++) {
    BigInt yi = points[i][1];
    BigInt lagrange = denoms[i];
    for (int j = 0; j < k; j++) {
      if (i != j) {
        lagrange = (lagrange * (-points[j][0])) % prime;
      }
    }
    secret = (secret + (yi * lagrange) % prime) % prime;
  }
  return (secret + prime) % prime;
}

// Extended Euclidean Algorithm for modular inverse (optimized)
BigInt modInverse(BigInt a, BigInt m) {
  if (m == BigInt.one) return BigInt.zero;

  BigInt m0 = m;
  BigInt y = BigInt.zero;
  BigInt x = BigInt.one;

  a = a % m;
  if (a < BigInt.zero) a += m;

  while (a > BigInt.one) {
    BigInt q = a ~/ m;
    BigInt t = m;

    m = a % m;
    a = t;

    t = y;
    y = x - q * y;
    x = t;
  }

  if (x < BigInt.zero) x += m0;
  return x;
}

void main(List<String> args) async {
  if (args.isEmpty) {
    print('Usage: dart secret_sharing.dart <input.json>');
    return;
  }
  final file = File(args[0]);
  final jsonStr = await file.readAsString();
  final data = jsonDecode(jsonStr);

  final k = data['keys']['k'];

  // Collect all shares
  List<List<BigInt>> allPoints = [];
  for (var key in data.keys) {
    if (key == 'keys') continue;
    var base = int.parse(data[key]['base']);
    var value = baseToDecimal(data[key]['value'], base);
    allPoints.add([BigInt.from(int.parse(key)), value]);
  }

  if (allPoints.length < k) {
    print('Not enough shares to reconstruct the secret.');
    return;
  }

  // Use the first k shares to reconstruct the secret
  List<List<BigInt>> points = allPoints.sublist(0, k);

  // Use the predefined large prime
  BigInt prime = LARGE_PRIME;

  print('Reconstructing secret...');
  BigInt secret = lagrangeInterpolation(points, prime);
  print('Recovered secret: $secret');

  // Check for wrong shares
  print('Checking for wrong shares...');
  List<List<BigInt>> wrongShares = [];

  // Optimize by computing polynomial coefficients once
  List<BigInt> coeffs = lagrangeCoefficients(points, prime);

  for (var pt in allPoints) {
    BigInt x = pt[0];
    BigInt y = pt[1];
    BigInt fx = evalPoly(coeffs, x, prime);
    if (fx != y) {
      wrongShares.add(pt);
    }
  }

  if (wrongShares.isNotEmpty) {
    print('Wrong shares detected:');
    for (var pt in wrongShares) {
      print('Share x=${pt[0]}, value=${pt[1]}');
    }
  } else {
    print('No wrong shares detected.');
  }
}

// Returns the next prime greater than or equal to n
BigInt nextPrime(BigInt n) {
  bool isPrime(BigInt x) {
    if (x < BigInt.two) return false;
    if (x == BigInt.two) return true;
    if (x % BigInt.two == BigInt.zero) return false;
    for (BigInt i = BigInt.from(3); i * i <= x; i += BigInt.two) {
      if (x % i == BigInt.zero) return false;
    }
    return true;
  }

  BigInt candidate = n;
  while (!isPrime(candidate)) {
    candidate += BigInt.one;
  }
  return candidate;
}

// Reconstructs the full polynomial coefficients using Lagrange interpolation (optimized)
List<BigInt> lagrangeCoefficients(List<List<BigInt>> points, BigInt prime) {
  int k = points.length;
  List<BigInt> coeffs = List.filled(k, BigInt.zero);

  // Precompute denominators
  List<BigInt> denoms = List.filled(k, BigInt.one);
  for (int i = 0; i < k; i++) {
    BigInt xi = points[i][0];
    for (int j = 0; j < k; j++) {
      if (i != j) {
        denoms[i] = (denoms[i] * (xi - points[j][0])) % prime;
      }
    }
    denoms[i] = modInverse(denoms[i], prime);
  }

  for (int i = 0; i < k; i++) {
    BigInt yi = points[i][1];

    // Compute the basis polynomial for this point
    List<BigInt> basis = List.filled(k, BigInt.zero);
    basis[0] = BigInt.one;
    int deg = 0;

    for (int j = 0; j < k; j++) {
      if (i != j) {
        BigInt xj = points[j][0];
        List<BigInt> term = [(-xj), BigInt.one];
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

// Optimized polynomial multiplication that only computes terms up to degree limit
List<BigInt> polyMulLimited(
    List<BigInt> a, List<BigInt> b, int limit, BigInt prime) {
  List<BigInt> res = List.filled(limit + 1, BigInt.zero);
  for (int i = 0; i < a.length && i <= limit; i++) {
    for (int j = 0; j < b.length && i + j <= limit; j++) {
      res[i + j] = (res[i + j] + a[i] * b[j]) % prime;
    }
  }
  return res;
}

// Evaluate polynomial at x (mod prime) - optimized with Horner's method
BigInt evalPoly(List<BigInt> coeffs, BigInt x, BigInt prime) {
  BigInt result = BigInt.zero;
  for (int i = coeffs.length - 1; i >= 0; i--) {
    result = (result * x + coeffs[i]) % prime;
  }
  return result;
}