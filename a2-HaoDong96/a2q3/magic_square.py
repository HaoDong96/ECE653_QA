'''Magic Square

https://en.wikipedia.org/wiki/Magic_square

A magic square is a n * n square grid filled with distinct positive integers in
the range 1, 2, ..., n^2 such that each cell contains a different integer and
the sum of the integers in each row, column, and diagonal is equal.

'''

from z3 import *


def solve_magic_square(n, r, c, val):
    solver = Solver()

    ### CREATE CONSTRAINTS AND LOAD STORE THEM IN THE SOLVER
    # nxn matrix of integer variables
    X = [[Int("x_%s_%s" % (i, j)) for j in range(n)]
         for i in range(n)]

    # each cell contains a value in {1, ..., n}
    cells_c = [And(1 <= X[i][j], X[i][j] <= pow(n, 2))
               for i in range(n) for j in range(n)]

    # each cell contains a dierent integer
    sq_c = [Distinct([X[i][j]
                      for i in range(n) for j in range(n)])]

    # sum
    sum_rows_c = [Sum(X[i_1]) == Sum(X[i_2]) for i_1 in range(n) for i_2 in range(n)]
    sum_cols_c = [Sum([X[i][j] for i in range(n)]) == Sum(X[0])
                  for j in range(n)]

    sum_diagonal_c1 = [Sum([X[i][i] for i in range(n)]) == Sum(X[0])]
    sum_diagonal_c2 = [Sum([X[i][n - i - 1] for i in range(n)]) == Sum(X[0])]
    # set val to X(r,c)
    set_c = [X[r][c] == val]

    magic_square_c = cells_c + sq_c + set_c + sum_rows_c + sum_cols_c \
                     + sum_diagonal_c1 + sum_diagonal_c2

    solver.add(magic_square_c)

    if solver.check() == sat:

        mod = solver.model()

        ### CREATE RESULT MAGIC SQUARE BASED ON THE MODEL FROM THE SOLVER
        res = [[mod.evaluate(X[i][j]).as_long() for j in range(n)]
               for i in range(n)]
        return res
    else:
        return None


def print_square(square):
    '''
    Prints a magic square as a square on the console
    '''
    n = len(square)

    assert n > 0
    for i in range(n):
        assert len(square[i]) == n

    for i in range(n):
        line = []
        for j in range(n):
            line.append(str(square[i][j]))
        print('\t'.join(line))


def puzzle(n, r, c, val):
    res = solve_magic_square(n, r, c, val)
    if res is None:
        print('No solution!')
    else:
        print('Solution:')
        print_square(res)


if __name__ == '__main__':
    n = 3
    r = 0
    c = 0
    val = 8
    puzzle(n, r, c, val)
