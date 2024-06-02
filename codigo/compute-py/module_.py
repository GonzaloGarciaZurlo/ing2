import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_

# Module: module_

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def fib(n):
        if (n) == (0):
            return 0
        elif (n) == (1):
            return 1
        elif True:
            return (default__.fib((n) - (1))) + (default__.fib((n) - (2)))

    @staticmethod
    def ComputeFib(n):
        b: int = int(0)
        d_0_i_: int
        d_0_i_ = 0
        d_1_c_: int
        d_1_c_ = 1
        b = 0
        while (d_0_i_) < (n):
            rhs0_ = d_1_c_
            rhs1_ = (d_1_c_) + (b)
            b = rhs0_
            d_1_c_ = rhs1_
            d_0_i_ = (d_0_i_) + (1)
        return b

    @staticmethod
    def Main(noArgsParameter__):
        d_2_n_: int
        d_2_n_ = 5
        d_3_fibo_: int
        out0_: int
        out0_ = default__.ComputeFib(d_2_n_)
        d_3_fibo_ = out0_
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Fibonachi of "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(d_2_n_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " is "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(d_3_fibo_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

