| Feature                     | Additive Secret Sharing                                    | Shamir’s Secret Sharing                                      |
|-----------------------------|------------------------------------------------------------|--------------------------------------------------------------|
| **Secret Splitting Method**  | Splits secret by random shares, secret is sum of shares    | Encodes secret as a constant in a polynomial                  |
| **Handling Large Numbers**   | Works natively with large numbers, no chunking required    | Struggles with large numbers, required chunking and recombination |
| **Threshold Flexibility**    | Requires exactly the threshold number of shares            | Any subset of participants above the threshold can reconstruct |
| **Reconstruction Complexity**| Simple sum and modulus                                     | Requires Lagrange interpolation over finite fields            |
| **Error Handling**           | Less prone to precision errors                             | Precision issues due to chunking large secrets                |
| **Use Cases**                | Secure multi-party computation, simple secret sharing      | Distributed systems, threshold cryptography, more complex protocols |


## Additive Secret Sharing

Additive secret sharing is a better fit because:

- It handles large integers directly.
- It simplifies the secret sharing and reconstruction process.
- It avoids the chunking issue that caused problems in the original Shamir-based approach.
