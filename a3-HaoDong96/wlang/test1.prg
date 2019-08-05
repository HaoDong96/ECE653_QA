{a := 1;
              b := -1;
              c := a + b; d := b - a;
              e := a * b; f := a / b};
              if a > 1 and a >= b then b := 3; 
              if a <= 1 or b < 3 then a := 1; 
              if false and not a = 1 then a := 1 else print_state; 
              skip;
              print_state;
              while (a < 3) or (b = 1) and true do {a := a + 1};
              assume b = -1;
              havoc c,d;
              assert a = 3;
              assert a = 2