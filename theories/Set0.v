Require Import Bool.
From BF Require Import Base Byte MIR.

Local Ltac exists_inverse x y :=
  destruct x; [discriminate | destruct x; [exists y; reflexivity |]].

Theorem nat_odd_has_inverse : forall x,
  x < 256 ->
  Nat.odd x = true ->
  exists y, x * y mod 256 = 1.
Proof.
  intros.
  (* 1 *) exists_inverse x 1.
  (* 3 *) exists_inverse x 171.
  (* 5 *) exists_inverse x 205.
  (* 7 *) exists_inverse x 183.
  (* 9 *) exists_inverse x 57.
  (* 11 *) exists_inverse x 163.
  (* 13 *) exists_inverse x 197.
  (* 15 *) exists_inverse x 239.
  (* 17 *) exists_inverse x 241.
  (* 19 *) exists_inverse x 27.
  (* 21 *) exists_inverse x 61.
  (* 23 *) exists_inverse x 167.
  (* 25 *) exists_inverse x 41.
  (* 27 *) exists_inverse x 19.
  (* 29 *) exists_inverse x 53.
  (* 31 *) exists_inverse x 223.
  (* 33 *) exists_inverse x 225.
  (* 35 *) exists_inverse x 139.
  (* 37 *) exists_inverse x 173.
  (* 39 *) exists_inverse x 151.
  (* 41 *) exists_inverse x 25.
  (* 43 *) exists_inverse x 131.
  (* 45 *) exists_inverse x 165.
  (* 47 *) exists_inverse x 207.
  (* 49 *) exists_inverse x 209.
  (* 51 *) exists_inverse x 251.
  (* 53 *) exists_inverse x 29.
  (* 55 *) exists_inverse x 135.
  (* 57 *) exists_inverse x 9.
  (* 59 *) exists_inverse x 243.
  (* 61 *) exists_inverse x 21.
  (* 63 *) exists_inverse x 191.
  (* 65 *) exists_inverse x 193.
  (* 67 *) exists_inverse x 107.
  (* 69 *) exists_inverse x 141.
  (* 71 *) exists_inverse x 119.
  (* 73 *) exists_inverse x 249.
  (* 75 *) exists_inverse x 99.
  (* 77 *) exists_inverse x 133.
  (* 79 *) exists_inverse x 175.
  (* 81 *) exists_inverse x 177.
  (* 83 *) exists_inverse x 219.
  (* 85 *) exists_inverse x 253.
  (* 87 *) exists_inverse x 103.
  (* 89 *) exists_inverse x 233.
  (* 91 *) exists_inverse x 211.
  (* 93 *) exists_inverse x 245.
  (* 95 *) exists_inverse x 159.
  (* 97 *) exists_inverse x 161.
  (* 99 *) exists_inverse x 75.
  (* 101 *) exists_inverse x 109.
  (* 103 *) exists_inverse x 87.
  (* 105 *) exists_inverse x 217.
  (* 107 *) exists_inverse x 67.
  (* 109 *) exists_inverse x 101.
  (* 111 *) exists_inverse x 143.
  (* 113 *) exists_inverse x 145.
  (* 115 *) exists_inverse x 187.
  (* 117 *) exists_inverse x 221.
  (* 119 *) exists_inverse x 71.
  (* 121 *) exists_inverse x 201.
  (* 123 *) exists_inverse x 179.
  (* 125 *) exists_inverse x 213.
  (* 127 *) exists_inverse x 127.
  (* 129 *) exists_inverse x 129.
  (* 131 *) exists_inverse x 43.
  (* 133 *) exists_inverse x 77.
  (* 135 *) exists_inverse x 55.
  (* 137 *) exists_inverse x 185.
  (* 139 *) exists_inverse x 35.
  (* 141 *) exists_inverse x 69.
  (* 143 *) exists_inverse x 111.
  (* 145 *) exists_inverse x 113.
  (* 147 *) exists_inverse x 155.
  (* 149 *) exists_inverse x 189.
  (* 151 *) exists_inverse x 39.
  (* 153 *) exists_inverse x 169.
  (* 155 *) exists_inverse x 147.
  (* 157 *) exists_inverse x 181.
  (* 159 *) exists_inverse x 95.
  (* 161 *) exists_inverse x 97.
  (* 163 *) exists_inverse x 11.
  (* 165 *) exists_inverse x 45.
  (* 167 *) exists_inverse x 23.
  (* 169 *) exists_inverse x 153.
  (* 171 *) exists_inverse x 3.
  (* 173 *) exists_inverse x 37.
  (* 175 *) exists_inverse x 79.
  (* 177 *) exists_inverse x 81.
  (* 179 *) exists_inverse x 123.
  (* 181 *) exists_inverse x 157.
  (* 183 *) exists_inverse x 7.
  (* 185 *) exists_inverse x 137.
  (* 187 *) exists_inverse x 115.
  (* 189 *) exists_inverse x 149.
  (* 191 *) exists_inverse x 63.
  (* 193 *) exists_inverse x 65.
  (* 195 *) exists_inverse x 235.
  (* 197 *) exists_inverse x 13.
  (* 199 *) exists_inverse x 247.
  (* 201 *) exists_inverse x 121.
  (* 203 *) exists_inverse x 227.
  (* 205 *) exists_inverse x 5.
  (* 207 *) exists_inverse x 47.
  (* 209 *) exists_inverse x 49.
  (* 211 *) exists_inverse x 91.
  (* 213 *) exists_inverse x 125.
  (* 215 *) exists_inverse x 231.
  (* 217 *) exists_inverse x 105.
  (* 219 *) exists_inverse x 83.
  (* 221 *) exists_inverse x 117.
  (* 223 *) exists_inverse x 31.
  (* 225 *) exists_inverse x 33.
  (* 227 *) exists_inverse x 203.
  (* 229 *) exists_inverse x 237.
  (* 231 *) exists_inverse x 215.
  (* 233 *) exists_inverse x 89.
  (* 235 *) exists_inverse x 195.
  (* 237 *) exists_inverse x 229.
  (* 239 *) exists_inverse x 15.
  (* 241 *) exists_inverse x 17.
  (* 243 *) exists_inverse x 59.
  (* 245 *) exists_inverse x 93.
  (* 247 *) exists_inverse x 199.
  (* 249 *) exists_inverse x 73.
  (* 251 *) exists_inverse x 51.
  (* 253 *) exists_inverse x 85.
  (* 255 *) exists_inverse x 255.
  intuition.
Qed.

Local Open Scope Z_scope.

Theorem Z_odd_has_inverse : forall x,
  x < 256 ->
  x >= 0 ->
  Z.odd x = true ->
  exists y, x * y mod 256 = 1.
Proof.
  intros.
  destruct x as [| x | x].
  - discriminate.
  - destruct x.
    { destruct x.
      { destruct x.
        { destruct x.
          { destruct x.
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 255 *) now exists 255.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 191 *) now exists 63.
                }
                (* 127 *) now exists 127.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 223 *) now exists 31.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 159 *) now exists 95.
                }
                (* 95 *) now exists 159.
              }
              (* 63 *) now exists 191.
            }
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 239 *) now exists 15.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 175 *) now exists 79.
                }
                (* 111 *) now exists 143.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 207 *) now exists 47.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 143 *) now exists 111.
                }
                (* 79 *) now exists 175.
              }
              (* 47 *) now exists 207.
            }
            (* 31 *) now exists 223.
          }
          { destruct x.
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 247 *) now exists 199.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 183 *) now exists 7.
                }
                (* 119 *) now exists 71.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 215 *) now exists 231.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 151 *) now exists 39.
                }
                (* 87 *) now exists 103.
              }
              (* 55 *) now exists 135.
            }
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 231 *) now exists 215.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 167 *) now exists 23.
                }
                (* 103 *) now exists 87.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 199 *) now exists 247.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 135 *) now exists 55.
                }
                (* 71 *) now exists 119.
              }
              (* 39 *) now exists 151.
            }
            (* 23 *) now exists 167.
          }
          (* 15 *) now exists 239.
        }
        { destruct x.
          { destruct x.
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 251 *) now exists 51.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 187 *) now exists 115.
                }
                (* 123 *) now exists 179.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 219 *) now exists 83.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 155 *) now exists 147.
                }
                (* 91 *) now exists 211.
              }
              (* 59 *) now exists 243.
            }
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 235 *) now exists 195.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 171 *) now exists 3.
                }
                (* 107 *) now exists 67.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 203 *) now exists 227.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 139 *) now exists 35.
                }
                (* 75 *) now exists 99.
              }
              (* 43 *) now exists 131.
            }
            (* 27 *) now exists 19.
          }
          { destruct x.
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 243 *) now exists 59.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 179 *) now exists 123.
                }
                (* 115 *) now exists 187.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 211 *) now exists 91.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 147 *) now exists 155.
                }
                (* 83 *) now exists 219.
              }
              (* 51 *) now exists 251.
            }
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 227 *) now exists 203.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 163 *) now exists 11.
                }
                (* 99 *) now exists 75.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 195 *) now exists 235.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 131 *) now exists 43.
                }
                (* 67 *) now exists 107.
              }
              (* 35 *) now exists 139.
            }
            (* 19 *) now exists 27.
          }
          (* 11 *) now exists 163.
        }
        (* 7 *) now exists 183.
      }
      { destruct x.
        { destruct x.
          { destruct x.
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 253 *) now exists 85.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 189 *) now exists 149.
                }
                (* 125 *) now exists 213.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 221 *) now exists 117.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 157 *) now exists 181.
                }
                (* 93 *) now exists 245.
              }
              (* 61 *) now exists 21.
            }
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 237 *) now exists 229.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 173 *) now exists 37.
                }
                (* 109 *) now exists 101.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 205 *) now exists 5.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 141 *) now exists 69.
                }
                (* 77 *) now exists 133.
              }
              (* 45 *) now exists 165.
            }
            (* 29 *) now exists 53.
          }
          { destruct x.
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 245 *) now exists 93.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 181 *) now exists 157.
                }
                (* 117 *) now exists 221.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 213 *) now exists 125.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 149 *) now exists 189.
                }
                (* 85 *) now exists 253.
              }
              (* 53 *) now exists 29.
            }
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 229 *) now exists 237.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 165 *) now exists 45.
                }
                (* 101 *) now exists 109.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 197 *) now exists 13.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 133 *) now exists 77.
                }
                (* 69 *) now exists 141.
              }
              (* 37 *) now exists 173.
            }
            (* 21 *) now exists 61.
          }
          (* 13 *) now exists 197.
        }
        { destruct x.
          { destruct x.
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 249 *) now exists 73.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 185 *) now exists 137.
                }
                (* 121 *) now exists 201.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 217 *) now exists 105.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 153 *) now exists 169.
                }
                (* 89 *) now exists 233.
              }
              (* 57 *) now exists 9.
            }
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 233 *) now exists 89.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 169 *) now exists 153.
                }
                (* 105 *) now exists 217.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 201 *) now exists 121.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 137 *) now exists 185.
                }
                (* 73 *) now exists 249.
              }
              (* 41 *) now exists 25.
            }
            (* 25 *) now exists 41.
          }
          { destruct x.
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 241 *) now exists 17.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 177 *) now exists 81.
                }
                (* 113 *) now exists 145.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 209 *) now exists 49.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 145 *) now exists 113.
                }
                (* 81 *) now exists 177.
              }
              (* 49 *) now exists 209.
            }
            { destruct x.
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 225 *) now exists 33.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 161 *) now exists 97.
                }
                (* 97 *) now exists 161.
              }
              { destruct x.
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 193 *) now exists 65.
                }
                { destruct x.
                  { destruct x; discriminate. }
                  { destruct x; discriminate. }
                  (* 129 *) now exists 129.
                }
                (* 65 *) now exists 193.
              }
              (* 33 *) now exists 225.
            }
            (* 17 *) now exists 241.
          }
          (* 9 *) now exists 57.
        }
        (* 5 *) now exists 205.
      }
      (* 3 *) now exists 171.
    }
    { discriminate. }
    { (* 1 *) now exists 1. }
  - apply Z.ge_le, Zle_not_lt in H0.
    exfalso. apply H0, Zlt_neg_0.
Qed.
