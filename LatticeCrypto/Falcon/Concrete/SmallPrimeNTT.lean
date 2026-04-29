/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

/-!
# NTT over small 31-bit primes for NTRU solving

Modular arithmetic and NTT operations over small 31-bit primes used in Falcon
key generation (NTRU equation solving). The primes satisfy:
- `(4/3) * 2^30 < p < 2^31` (so `2p < 2^32 < 3p`)
- `p ≡ 1 (mod 2048)`

Values modulo `p` are in `[0, p)`. Montgomery multiplication computes
`(a * b * R⁻¹) mod p` where `R = 2^32 mod p`.

Each entry of the `PRIMES` table stores:
- `p`: the prime modulus
- `p0i`: `-1/p mod 2^32`
- `R2`: `2^64 mod p`
- `g`: primitive 2048-th root of unity mod p (in Montgomery form)
- `ig`: `1/g mod p` (in Montgomery form)
- `s`: CRT scaling factor (in Montgomery form)

Ported from `c-fn-dsa/kgen_mp31.c` and `c-fn-dsa/kgen_inner.h`.
-/


namespace Falcon.Concrete.SmallPrimeNTT

/-! ## Modular arithmetic helpers -/

@[inline] def tbmask (x : UInt32) : UInt32 :=
  (x.toInt32 >>> (31 : Int32)).toUInt32

@[inline] def mp_set (v : Int32) (p : UInt32) : UInt32 :=
  v.toUInt32 + (p &&& tbmask v.toUInt32)

@[inline] def mp_norm (x : UInt32) (p : UInt32) : Int32 :=
  let x' := x - (p &&& tbmask ((p >>> (1 : UInt32)) - x))
  x'.toInt32

@[inline] def mp_R (p : UInt32) : UInt32 :=
  0 - (p <<< (1 : UInt32))

@[inline] def mp_hR (p : UInt32) : UInt32 :=
  ((1 : UInt32) <<< (31 : UInt32)) - p

@[inline] def mp_add (a b p : UInt32) : UInt32 :=
  let d := a + b - p
  d + (p &&& tbmask d)

@[inline] def mp_sub (a b p : UInt32) : UInt32 :=
  let d := a - b
  d + (p &&& tbmask d)

@[inline] def mp_half (a p : UInt32) : UInt32 :=
  (a + (p &&& (0 - (a &&& 1)))) >>> (1 : UInt32)

@[inline] def mp_montymul (a b p p0i : UInt32) : UInt32 :=
  let z : UInt64 := a.toUInt64 * b.toUInt64
  let w : UInt32 := z.toUInt32 * p0i
  let d : UInt32 := ((z + w.toUInt64 * p.toUInt64) >>> (32 : UInt64)).toUInt32 - p
  d + (p &&& tbmask d)

/-! ## PRIMES table

Each entry is `(p, p0i, R2, g, ig, s)`. We include the first 25 primes,
which suffice for Falcon-512 and Falcon-1024 key generation. -/

structure SmallPrime where
  p   : UInt32
  p0i : UInt32
  R2  : UInt32
  g   : UInt32
  ig  : UInt32
  s   : UInt32
  deriving Repr, Inhabited

def PRIMES : Array SmallPrime := #[
  ⟨2147473409, 2042615807,  419348484, 1790111537,  786166065,      20478⟩,
  ⟨2147389441, 1862176767, 1141604340,  677655126, 2024968256,  942807490⟩,
  ⟨2147387393, 1472104447,  554514419,  563781659, 1438853699,  511282737⟩,
  ⟨2147377153, 3690881023,  269819887,  978644358, 1971237828, 1936446844⟩,
  ⟨2147358721, 3720222719,  153618407, 1882929796,  289507384,  264920030⟩,
  ⟨2147352577, 2147352575,    3145700,  875644459, 1993867586, 1197387618⟩,
  ⟨2147346433,  498984959,  154699745, 1268990641, 1559885885, 2112514368⟩,
  ⟨2147338241, 2478688255,  826591197,  304701980,  207126964,  842573420⟩,
  ⟨2147309569, 1908234239,  964657100, 1953449942,  309167499,   75092579⟩,
  ⟨2147297281, 1774004223, 1503608772,  353848817, 1726802198, 2084007226⟩,
  ⟨2147295233, 1006444543,  279363522,  632955619,  419515149,   38880066⟩,
  ⟨2147239937, 2881243135, 1383813014,  710717957,  756383674,  706593520⟩,
  ⟨2147235841,  867973119,  848351122, 1627458017, 1867341538, 1260600213⟩,
  ⟨2147217409, 4277923839,  100122496, 1700895952, 1076153660,  370621817⟩,
  ⟨2147205121, 1878769663, 1111621492,   44667394, 1556218865,   32248737⟩,
  ⟨2147196929, 1543217151,  310009707, 1302747296, 1775932980, 1745280407⟩,
  ⟨2147178497, 3518715903, 1006651223,  995615578, 1904695444,  546877831⟩,
  ⟨2147100673, 1505372159,  520918771,   32821017,  801131396, 1402329446⟩,
  ⟨2147082241, 4227457023,  385646296,  671813454,  349022278, 1235641740⟩,
  ⟨2147074049, 1878638591, 1198259916,   22548867,  381743482,  316764378⟩,
  ⟨2147051521,   96036863, 1908098729, 1744576193,  129309952, 1045517086⟩,
  ⟨2147043329, 1538869247,  440645275,  848789527,  259769898,   74455690⟩,
  ⟨2147039233, 2209953791, 2055370389, 1117428534, 1471147502,  119673623⟩,
  ⟨2146988033, 1324904447, 1363381819, 2041738204,  478044407,  147722658⟩,
  ⟨2146963457, 2130186239,  325123596, 2068278376,  875801492, 1306038870⟩
]

/-! ## Bit-reversal table (10-bit) -/

private def REV10 : Array UInt16 := #[
     0,  512,  256,  768,  128,  640,  384,  896,   64,  576,  320,  832,
   192,  704,  448,  960,   32,  544,  288,  800,  160,  672,  416,  928,
    96,  608,  352,  864,  224,  736,  480,  992,   16,  528,  272,  784,
   144,  656,  400,  912,   80,  592,  336,  848,  208,  720,  464,  976,
    48,  560,  304,  816,  176,  688,  432,  944,  112,  624,  368,  880,
   240,  752,  496, 1008,    8,  520,  264,  776,  136,  648,  392,  904,
    72,  584,  328,  840,  200,  712,  456,  968,   40,  552,  296,  808,
   168,  680,  424,  936,  104,  616,  360,  872,  232,  744,  488, 1000,
    24,  536,  280,  792,  152,  664,  408,  920,   88,  600,  344,  856,
   216,  728,  472,  984,   56,  568,  312,  824,  184,  696,  440,  952,
   120,  632,  376,  888,  248,  760,  504, 1016,    4,  516,  260,  772,
   132,  644,  388,  900,   68,  580,  324,  836,  196,  708,  452,  964,
    36,  548,  292,  804,  164,  676,  420,  932,  100,  612,  356,  868,
   228,  740,  484,  996,   20,  532,  276,  788,  148,  660,  404,  916,
    84,  596,  340,  852,  212,  724,  468,  980,   52,  564,  308,  820,
   180,  692,  436,  948,  116,  628,  372,  884,  244,  756,  500, 1012,
    12,  524,  268,  780,  140,  652,  396,  908,   76,  588,  332,  844,
   204,  716,  460,  972,   44,  556,  300,  812,  172,  684,  428,  940,
   108,  620,  364,  876,  236,  748,  492, 1004,   28,  540,  284,  796,
   156,  668,  412,  924,   92,  604,  348,  860,  220,  732,  476,  988,
    60,  572,  316,  828,  188,  700,  444,  956,  124,  636,  380,  892,
   252,  764,  508, 1020,    2,  514,  258,  770,  130,  642,  386,  898,
    66,  578,  322,  834,  194,  706,  450,  962,   34,  546,  290,  802,
   162,  674,  418,  930,   98,  610,  354,  866,  226,  738,  482,  994,
    18,  530,  274,  786,  146,  658,  402,  914,   82,  594,  338,  850,
   210,  722,  466,  978,   50,  562,  306,  818,  178,  690,  434,  946,
   114,  626,  370,  882,  242,  754,  498, 1010,   10,  522,  266,  778,
   138,  650,  394,  906,   74,  586,  330,  842,  202,  714,  458,  970,
    42,  554,  298,  810,  170,  682,  426,  938,  106,  618,  362,  874,
   234,  746,  490, 1002,   26,  538,  282,  794,  154,  666,  410,  922,
    90,  602,  346,  858,  218,  730,  474,  986,   58,  570,  314,  826,
   186,  698,  442,  954,  122,  634,  378,  890,  250,  762,  506, 1018,
     6,  518,  262,  774,  134,  646,  390,  902,   70,  582,  326,  838,
   198,  710,  454,  966,   38,  550,  294,  806,  166,  678,  422,  934,
   102,  614,  358,  870,  230,  742,  486,  998,   22,  534,  278,  790,
   150,  662,  406,  918,   86,  598,  342,  854,  214,  726,  470,  982,
    54,  566,  310,  822,  182,  694,  438,  950,  118,  630,  374,  886,
   246,  758,  502, 1014,   14,  526,  270,  782,  142,  654,  398,  910,
    78,  590,  334,  846,  206,  718,  462,  974,   46,  558,  302,  814,
   174,  686,  430,  942,  110,  622,  366,  878,  238,  750,  494, 1006,
    30,  542,  286,  798,  158,  670,  414,  926,   94,  606,  350,  862,
   222,  734,  478,  990,   62,  574,  318,  830,  190,  702,  446,  958,
   126,  638,  382,  894,  254,  766,  510, 1022,    1,  513,  257,  769,
   129,  641,  385,  897,   65,  577,  321,  833,  193,  705,  449,  961,
    33,  545,  289,  801,  161,  673,  417,  929,   97,  609,  353,  865,
   225,  737,  481,  993,   17,  529,  273,  785,  145,  657,  401,  913,
    81,  593,  337,  849,  209,  721,  465,  977,   49,  561,  305,  817,
   177,  689,  433,  945,  113,  625,  369,  881,  241,  753,  497, 1009,
     9,  521,  265,  777,  137,  649,  393,  905,   73,  585,  329,  841,
   201,  713,  457,  969,   41,  553,  297,  809,  169,  681,  425,  937,
   105,  617,  361,  873,  233,  745,  489, 1001,   25,  537,  281,  793,
   153,  665,  409,  921,   89,  601,  345,  857,  217,  729,  473,  985,
    57,  569,  313,  825,  185,  697,  441,  953,  121,  633,  377,  889,
   249,  761,  505, 1017,    5,  517,  261,  773,  133,  645,  389,  901,
    69,  581,  325,  837,  197,  709,  453,  965,   37,  549,  293,  805,
   165,  677,  421,  933,  101,  613,  357,  869,  229,  741,  485,  997,
    21,  533,  277,  789,  149,  661,  405,  917,   85,  597,  341,  853,
   213,  725,  469,  981,   53,  565,  309,  821,  181,  693,  437,  949,
   117,  629,  373,  885,  245,  757,  501, 1013,   13,  525,  269,  781,
   141,  653,  397,  909,   77,  589,  333,  845,  205,  717,  461,  973,
    45,  557,  301,  813,  173,  685,  429,  941,  109,  621,  365,  877,
   237,  749,  493, 1005,   29,  541,  285,  797,  157,  669,  413,  925,
    93,  605,  349,  861,  221,  733,  477,  989,   61,  573,  317,  829,
   189,  701,  445,  957,  125,  637,  381,  893,  253,  765,  509, 1021,
     3,  515,  259,  771,  131,  643,  387,  899,   67,  579,  323,  835,
   195,  707,  451,  963,   35,  547,  291,  803,  163,  675,  419,  931,
    99,  611,  355,  867,  227,  739,  483,  995,   19,  531,  275,  787,
   147,  659,  403,  915,   83,  595,  339,  851,  211,  723,  467,  979,
    51,  563,  307,  819,  179,  691,  435,  947,  115,  627,  371,  883,
   243,  755,  499, 1011,   11,  523,  267,  779,  139,  651,  395,  907,
    75,  587,  331,  843,  203,  715,  459,  971,   43,  555,  299,  811,
   171,  683,  427,  939,  107,  619,  363,  875,  235,  747,  491, 1003,
    27,  539,  283,  795,  155,  667,  411,  923,   91,  603,  347,  859,
   219,  731,  475,  987,   59,  571,  315,  827,  187,  699,  443,  955,
   123,  635,  379,  891,  251,  763,  507, 1019,    7,  519,  263,  775,
   135,  647,  391,  903,   71,  583,  327,  839,  199,  711,  455,  967,
    39,  551,  295,  807,  167,  679,  423,  935,  103,  615,  359,  871,
   231,  743,  487,  999,   23,  535,  279,  791,  151,  663,  407,  919,
    87,  599,  343,  855,  215,  727,  471,  983,   55,  567,  311,  823,
   183,  695,  439,  951,  119,  631,  375,  887,  247,  759,  503, 1015,
    15,  527,  271,  783,  143,  655,  399,  911,   79,  591,  335,  847,
   207,  719,  463,  975,   47,  559,  303,  815,  175,  687,  431,  943,
   111,  623,  367,  879,  239,  751,  495, 1007,   31,  543,  287,  799,
   159,  671,  415,  927,   95,  607,  351,  863,  223,  735,  479,  991,
    63,  575,  319,  831,  191,  703,  447,  959,  127,  639,  383,  895,
   255,  767,  511, 1023
]

/-! ## Polynomial conversion helpers -/

def mp_set_small (logn : Nat) (f : Array Int8) (p : UInt32) :
    Array UInt32 := Id.run do
  let n := 1 <<< logn
  let mut d : Array UInt32 := Array.replicate n (0 : UInt32)
  for i in [0:n] do
    d := d.set! i (mp_set (f.getD i 0).toInt32 p)
  return d

def poly_mp_set (logn : Nat) (f : Array UInt32) (p : UInt32) :
    Array UInt32 := Id.run do
  let n := 1 <<< logn
  let mut d := f
  for i in [0:n] do
    let v := d.getD i 0
    d := d.set! i (mp_set v.toInt32 p)
  return d

def poly_mp_norm (logn : Nat) (f : Array UInt32) (p : UInt32) :
    Array UInt32 := Id.run do
  let n := 1 <<< logn
  let mut d := f
  for i in [0:n] do
    let v := d.getD i 0
    d := d.set! i (mp_norm v p).toUInt32
  return d

/-! ## Twiddle factor generation -/

def mp_mkgm (logn : Nat) (g : UInt32) (p p0i : UInt32) :
    Array UInt32 := Id.run do
  let n := 1 <<< logn
  let mut g' := g
  for _ in [logn:10] do
    g' := mp_montymul g' g' p p0i
  let k := 10 - logn
  let mut gm : Array UInt32 := Array.replicate n (0 : UInt32)
  let mut x1 := mp_R p
  for i in [0:n] do
    let j := (REV10.getD (i <<< k) 0).toNat
    gm := gm.set! j x1
    if i + 1 < n then
      x1 := mp_montymul x1 g' p p0i
  return gm

def mp_mkgmigm (logn : Nat) (g ig : UInt32) (p p0i : UInt32) :
    Array UInt32 × Array UInt32 := Id.run do
  let n := 1 <<< logn
  let mut g' := g
  let mut ig' := ig
  for _ in [logn:10] do
    g' := mp_montymul g' g' p p0i
    ig' := mp_montymul ig' ig' p p0i
  let k := 10 - logn
  let mut gm : Array UInt32 := Array.replicate n (0 : UInt32)
  let mut igm : Array UInt32 := Array.replicate n (0 : UInt32)
  let mut x1 := mp_R p
  let mut x2 := mp_hR p
  for i in [0:n] do
    let j := (REV10.getD (i <<< k) 0).toNat
    gm := gm.set! j x1
    igm := igm.set! j x2
    if i + 1 < n then
      x1 := mp_montymul x1 g' p p0i
      x2 := mp_montymul x2 ig' p p0i
  return (gm, igm)

/-! ## Forward NTT

Cooley-Tukey butterfly with two-layer merging for fewer memory accesses. -/

def mp_NTT (logn : Nat) (a : Array UInt32) (gm : Array UInt32)
    (p p0i : UInt32) : Array UInt32 := Id.run do
  if logn == 0 then return a
  let mut a := a
  if logn == 1 then
    let s := gm.getD 1 0
    let x0 := a.getD 0 0
    let x1 := mp_montymul (a.getD 1 0) s p p0i
    a := a.set! 0 (mp_add x0 x1 p)
    a := a.set! 1 (mp_sub x0 x1 p)
    return a

  let mut lm : Nat := 0
  let mut t : Nat := 0

  if logn % 2 != 0 then
    t := 1 <<< (logn - 1)
    let s := gm.getD 1 0
    for i in [0:t] do
      let x0 := a.getD i 0
      let x1 := mp_montymul (a.getD (i + t) 0) s p p0i
      a := a.set! i (mp_add x0 x1 p)
      a := a.set! (i + t) (mp_sub x0 x1 p)
    lm := 1
  else
    t := 1 <<< logn
    lm := 0

  while lm + 3 < logn do
    let m := 1 <<< lm
    let ht := t / 2
    let qt := ht / 2
    let mut j0 : Nat := 0
    for i in [0:m] do
      let idx := i + m
      let s := gm.getD idx 0
      let s0 := gm.getD (idx * 2) 0
      let s1 := gm.getD (idx * 2 + 1) 0
      for j in [0:qt] do
        let k0 := j0 + j
        let k1 := k0 + qt
        let k2 := k0 + ht
        let k3 := k0 + ht + qt
        let mut x0 := a.getD k0 0
        let mut x1 := a.getD k1 0
        let mut x2 := a.getD k2 0
        let mut x3 := a.getD k3 0

        let tt := mp_montymul x2 s p p0i
        x2 := mp_sub x0 tt p
        x0 := mp_add x0 tt p

        let tt := mp_montymul x3 s p p0i
        x3 := mp_sub x1 tt p
        x1 := mp_add x1 tt p

        let tt := mp_montymul x1 s0 p p0i
        x1 := mp_sub x0 tt p
        x0 := mp_add x0 tt p

        let tt := mp_montymul x3 s1 p p0i
        x3 := mp_sub x2 tt p
        x2 := mp_add x2 tt p

        a := a.set! k0 x0
        a := a.set! k1 x1
        a := a.set! k2 x2
        a := a.set! k3 x3
      j0 := j0 + t
    t := qt
    lm := lm + 2

  let m := 1 <<< (logn - 2)
  for i in [0:m] do
    let idx := i + m
    let s := gm.getD idx 0
    let s0 := gm.getD (idx * 2) 0
    let s1 := gm.getD (idx * 2 + 1) 0
    let mut x0 := a.getD (i * 4) 0
    let mut x1 := a.getD (i * 4 + 1) 0
    let mut x2 := a.getD (i * 4 + 2) 0
    let mut x3 := a.getD (i * 4 + 3) 0

    let tt := mp_montymul x2 s p p0i
    x2 := mp_sub x0 tt p
    x0 := mp_add x0 tt p

    let tt := mp_montymul x3 s p p0i
    x3 := mp_sub x1 tt p
    x1 := mp_add x1 tt p

    let tt := mp_montymul x1 s0 p p0i
    x1 := mp_sub x0 tt p
    x0 := mp_add x0 tt p

    let tt := mp_montymul x3 s1 p p0i
    x3 := mp_sub x2 tt p
    x2 := mp_add x2 tt p

    a := a.set! (i * 4) x0
    a := a.set! (i * 4 + 1) x1
    a := a.set! (i * 4 + 2) x2
    a := a.set! (i * 4 + 3) x3
  return a

/-! ## Inverse NTT

Gentleman-Sande butterfly with two-layer merging. -/

def mp_iNTT (logn : Nat) (a : Array UInt32) (igm : Array UInt32)
    (p p0i : UInt32) : Array UInt32 := Id.run do
  if logn == 0 then return a
  let mut a := a
  if logn == 1 then
    let s := igm.getD 1 0
    let x0 := a.getD 0 0
    let x1 := a.getD 1 0
    a := a.set! 0 (mp_half (mp_add x0 x1 p) p)
    a := a.set! 1 (mp_montymul (mp_sub x0 x1 p) s p p0i)
    return a

  let qn := 1 <<< (logn - 2)
  for i in [0:qn] do
    let idx := i + qn
    let s0 := igm.getD (idx * 2) 0
    let s1 := igm.getD (idx * 2 + 1) 0
    let s := igm.getD idx 0

    let mut x0 := a.getD (i * 4) 0
    let mut x1 := a.getD (i * 4 + 1) 0
    let mut x2 := a.getD (i * 4 + 2) 0
    let mut x3 := a.getD (i * 4 + 3) 0

    let tt := mp_sub x0 x1 p
    x0 := mp_half (mp_add x0 x1 p) p
    x1 := mp_montymul tt s0 p p0i

    let tt := mp_sub x2 x3 p
    x2 := mp_half (mp_add x2 x3 p) p
    x3 := mp_montymul tt s1 p p0i

    let tt := mp_sub x0 x2 p
    x0 := mp_half (mp_add x0 x2 p) p
    x2 := mp_montymul tt s p p0i

    let tt := mp_sub x1 x3 p
    x1 := mp_half (mp_add x1 x3 p) p
    x3 := mp_montymul tt s p p0i

    a := a.set! (i * 4) x0
    a := a.set! (i * 4 + 1) x1
    a := a.set! (i * 4 + 2) x2
    a := a.set! (i * 4 + 3) x3

  let mut t : Nat := 4

  let mut lm : Nat := 2
  while lm + 1 < logn do
    let hm := 1 <<< (logn - 1 - lm)
    let qm := hm / 2
    let dt := t * 2
    let ft := t * 4
    let mut j0 : Nat := 0
    for i in [0:qm] do
      let idx := i + qm
      let s0 := igm.getD (idx * 2) 0
      let s1 := igm.getD (idx * 2 + 1) 0
      let s := igm.getD idx 0
      for j in [0:t] do
        let k0 := j0 + j
        let k1 := k0 + t
        let k2 := k0 + dt
        let k3 := k0 + t + dt
        let mut x0 := a.getD k0 0
        let mut x1 := a.getD k1 0
        let mut x2 := a.getD k2 0
        let mut x3 := a.getD k3 0

        let tt := mp_sub x0 x1 p
        x0 := mp_half (mp_add x0 x1 p) p
        x1 := mp_montymul tt s0 p p0i

        let tt := mp_sub x2 x3 p
        x2 := mp_half (mp_add x2 x3 p) p
        x3 := mp_montymul tt s1 p p0i

        let tt := mp_sub x0 x2 p
        x0 := mp_half (mp_add x0 x2 p) p
        x2 := mp_montymul tt s p p0i

        let tt := mp_sub x1 x3 p
        x1 := mp_half (mp_add x1 x3 p) p
        x3 := mp_montymul tt s p p0i

        a := a.set! k0 x0
        a := a.set! k1 x1
        a := a.set! k2 x2
        a := a.set! k3 x3
      j0 := j0 + ft
    t := ft
    lm := lm + 2

  if logn % 2 != 0 then
    let hn := 1 <<< (logn - 1)
    let s := igm.getD 1 0
    for i in [0:hn] do
      let x0 := a.getD i 0
      let x1 := a.getD (i + hn) 0
      a := a.set! i (mp_half (mp_add x0 x1 p) p)
      a := a.set! (i + hn) (mp_montymul (mp_sub x0 x1 p) s p p0i)
  return a

/-- Compute `2^(31*e) mod p` using repeated squaring. -/
def mp_Rx31 (e : Nat) (p p0i R2 : UInt32) : UInt32 := Id.run do
  let mut x := mp_half R2 p
  let mut d : UInt32 := 1
  let mut e := e
  while e != 0 do
    if e % 2 != 0 then
      d := mp_montymul d x p p0i
    e := e / 2
    if e != 0 then
      x := mp_montymul x x p p0i
  return d

end Falcon.Concrete.SmallPrimeNTT
