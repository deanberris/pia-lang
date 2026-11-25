# Work in progress: the Kraft lemma for Pia.Compress.Huffman

`kraft.pia` holds lemmas that prove `kraft l n <= 32768 ==> room l n 1`, the
precondition Huffman.decode needs (with `tab_from t l n 1`) for its theorem
that the symbol decoded is the one whose canonical code is the bits read.
Not built by Bazel; paste it above `u16at` in lib/Pia/Compress/Huffman.pia.

- Round 1: 56 of 60 goals. Round 2, with stepping asserts: 121 of 129.
- What fails: the facts that mix u32 values with `int` (`int (first_code ...)`,
  `int (kraft ...)`), such as `first_code l n b = 2 * (first_code l n b' +
  len_count l n b')` in int, time out. `room_at`'s case split over the
  length b proves for b = 1 to 14; there each case is linear, since
  `weight b` and `B.pow2 b` are constants.
- Next: drop `int` and the induction over lengths. Make `ksum` u32, and
  prove each fixed length by unfolding (`@fuel(16)`), where `first_code`
  and `ksum` are linear in the counts with constant coefficients.
