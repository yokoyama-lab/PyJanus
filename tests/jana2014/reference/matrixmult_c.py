"""Matrix multiplication routed through a Crout LU decomposition.

Asserted: B is decomposed, used and recomposed, so it comes back exactly as it
went in, and n is untouched. The product accumulated into A depends on how
multLD and multU split the decomposition between them, which is a property of
this factorisation-based encoding rather than of the product.
"""

GARBAGE = []

PARTIAL = "the product accumulated into A, which depends on how multLD and multU split the factorisation"

B = [[2, 4, 4], [4, 1, 1], [2, 3, 4]]


def expected():
  return {"B": B, "n": len(B)}
