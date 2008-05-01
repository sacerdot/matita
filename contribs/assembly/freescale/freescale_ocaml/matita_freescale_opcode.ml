type mcu_type =
HC05
 | HC08
 | HCS08
 | RS08
;;

let mcu_type_rec =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function m -> 
(match m with 
   HC05 -> p
 | HC08 -> p1
 | HCS08 -> p2
 | RS08 -> p3)
)))))
;;

let mcu_type_rect =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function m -> 
(match m with 
   HC05 -> p
 | HC08 -> p1
 | HCS08 -> p2
 | RS08 -> p3)
)))))
;;

type instr_mode =
MODE_INH
 | MODE_INHA
 | MODE_INHX
 | MODE_INHH
 | MODE_INHX0ADD
 | MODE_INHX1ADD
 | MODE_INHX2ADD
 | MODE_IMM1
 | MODE_IMM1EXT
 | MODE_IMM2
 | MODE_DIR1
 | MODE_DIR2
 | MODE_IX0
 | MODE_IX1
 | MODE_IX2
 | MODE_SP1
 | MODE_SP2
 | MODE_DIR1_to_DIR1
 | MODE_IMM1_to_DIR1
 | MODE_IX0p_to_DIR1
 | MODE_DIR1_to_IX0p
 | MODE_INHA_and_IMM1
 | MODE_INHX_and_IMM1
 | MODE_IMM1_and_IMM1
 | MODE_DIR1_and_IMM1
 | MODE_IX0_and_IMM1
 | MODE_IX0p_and_IMM1
 | MODE_IX1_and_IMM1
 | MODE_IX1p_and_IMM1
 | MODE_SP1_and_IMM1
 | MODE_DIRn of Matita_freescale_aux_bases.oct
 | MODE_DIRn_and_IMM1 of Matita_freescale_aux_bases.oct
 | MODE_TNY of Matita_freescale_exadecim.exadecim
 | MODE_SRT of Matita_freescale_aux_bases.bitrigesim
;;

let instr_mode_rec =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function p5 -> (function p6 -> (function p7 -> (function p8 -> (function p9 -> (function p10 -> (function p11 -> (function p12 -> (function p13 -> (function p14 -> (function p15 -> (function p16 -> (function p17 -> (function p18 -> (function p19 -> (function p20 -> (function p21 -> (function p22 -> (function p23 -> (function p24 -> (function p25 -> (function p26 -> (function p27 -> (function p28 -> (function p29 -> (function f -> (function f1 -> (function f2 -> (function f3 -> (function i -> 
(match i with 
   MODE_INH -> p
 | MODE_INHA -> p1
 | MODE_INHX -> p2
 | MODE_INHH -> p3
 | MODE_INHX0ADD -> p4
 | MODE_INHX1ADD -> p5
 | MODE_INHX2ADD -> p6
 | MODE_IMM1 -> p7
 | MODE_IMM1EXT -> p8
 | MODE_IMM2 -> p9
 | MODE_DIR1 -> p10
 | MODE_DIR2 -> p11
 | MODE_IX0 -> p12
 | MODE_IX1 -> p13
 | MODE_IX2 -> p14
 | MODE_SP1 -> p15
 | MODE_SP2 -> p16
 | MODE_DIR1_to_DIR1 -> p17
 | MODE_IMM1_to_DIR1 -> p18
 | MODE_IX0p_to_DIR1 -> p19
 | MODE_DIR1_to_IX0p -> p20
 | MODE_INHA_and_IMM1 -> p21
 | MODE_INHX_and_IMM1 -> p22
 | MODE_IMM1_and_IMM1 -> p23
 | MODE_DIR1_and_IMM1 -> p24
 | MODE_IX0_and_IMM1 -> p25
 | MODE_IX0p_and_IMM1 -> p26
 | MODE_IX1_and_IMM1 -> p27
 | MODE_IX1p_and_IMM1 -> p28
 | MODE_SP1_and_IMM1 -> p29
 | MODE_DIRn(o) -> (f o)
 | MODE_DIRn_and_IMM1(o) -> (f1 o)
 | MODE_TNY(e) -> (f2 e)
 | MODE_SRT(b) -> (f3 b))
)))))))))))))))))))))))))))))))))))
;;

let instr_mode_rect =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function p5 -> (function p6 -> (function p7 -> (function p8 -> (function p9 -> (function p10 -> (function p11 -> (function p12 -> (function p13 -> (function p14 -> (function p15 -> (function p16 -> (function p17 -> (function p18 -> (function p19 -> (function p20 -> (function p21 -> (function p22 -> (function p23 -> (function p24 -> (function p25 -> (function p26 -> (function p27 -> (function p28 -> (function p29 -> (function f -> (function f1 -> (function f2 -> (function f3 -> (function i -> 
(match i with 
   MODE_INH -> p
 | MODE_INHA -> p1
 | MODE_INHX -> p2
 | MODE_INHH -> p3
 | MODE_INHX0ADD -> p4
 | MODE_INHX1ADD -> p5
 | MODE_INHX2ADD -> p6
 | MODE_IMM1 -> p7
 | MODE_IMM1EXT -> p8
 | MODE_IMM2 -> p9
 | MODE_DIR1 -> p10
 | MODE_DIR2 -> p11
 | MODE_IX0 -> p12
 | MODE_IX1 -> p13
 | MODE_IX2 -> p14
 | MODE_SP1 -> p15
 | MODE_SP2 -> p16
 | MODE_DIR1_to_DIR1 -> p17
 | MODE_IMM1_to_DIR1 -> p18
 | MODE_IX0p_to_DIR1 -> p19
 | MODE_DIR1_to_IX0p -> p20
 | MODE_INHA_and_IMM1 -> p21
 | MODE_INHX_and_IMM1 -> p22
 | MODE_IMM1_and_IMM1 -> p23
 | MODE_DIR1_and_IMM1 -> p24
 | MODE_IX0_and_IMM1 -> p25
 | MODE_IX0p_and_IMM1 -> p26
 | MODE_IX1_and_IMM1 -> p27
 | MODE_IX1p_and_IMM1 -> p28
 | MODE_SP1_and_IMM1 -> p29
 | MODE_DIRn(o) -> (f o)
 | MODE_DIRn_and_IMM1(o) -> (f1 o)
 | MODE_TNY(e) -> (f2 e)
 | MODE_SRT(b) -> (f3 b))
)))))))))))))))))))))))))))))))))))
;;

type opcode =
ADC
 | ADD
 | AIS
 | AIX
 | AND
 | ASL
 | ASR
 | BCC
 | BCLRn
 | BCS
 | BEQ
 | BGE
 | BGND
 | BGT
 | BHCC
 | BHCS
 | BHI
 | BIH
 | BIL
 | BIT
 | BLE
 | BLS
 | BLT
 | BMC
 | BMI
 | BMS
 | BNE
 | BPL
 | BRA
 | BRCLRn
 | BRN
 | BRSETn
 | BSETn
 | BSR
 | CBEQA
 | CBEQX
 | CLC
 | CLI
 | CLR
 | CMP
 | COM
 | CPHX
 | CPX
 | DAA
 | DBNZ
 | DEC
 | DIV
 | EOR
 | INC
 | JMP
 | JSR
 | LDA
 | LDHX
 | LDX
 | LSR
 | MOV
 | MUL
 | NEG
 | NOP
 | NSA
 | ORA
 | PSHA
 | PSHH
 | PSHX
 | PULA
 | PULH
 | PULX
 | ROL
 | ROR
 | RSP
 | RTI
 | RTS
 | SBC
 | SEC
 | SEI
 | SHA
 | SLA
 | STA
 | STHX
 | STOP
 | STX
 | SUB
 | SWI
 | TAP
 | TAX
 | TPA
 | TST
 | TSX
 | TXA
 | TXS
 | WAIT
;;

let opcode_rec =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function p5 -> (function p6 -> (function p7 -> (function p8 -> (function p9 -> (function p10 -> (function p11 -> (function p12 -> (function p13 -> (function p14 -> (function p15 -> (function p16 -> (function p17 -> (function p18 -> (function p19 -> (function p20 -> (function p21 -> (function p22 -> (function p23 -> (function p24 -> (function p25 -> (function p26 -> (function p27 -> (function p28 -> (function p29 -> (function p30 -> (function p31 -> (function p32 -> (function p33 -> (function p34 -> (function p35 -> (function p36 -> (function p37 -> (function p38 -> (function p39 -> (function p40 -> (function p41 -> (function p42 -> (function p43 -> (function p44 -> (function p45 -> (function p46 -> (function p47 -> (function p48 -> (function p49 -> (function p50 -> (function p51 -> (function p52 -> (function p53 -> (function p54 -> (function p55 -> (function p56 -> (function p57 -> (function p58 -> (function p59 -> (function p60 -> (function p61 -> (function p62 -> (function p63 -> (function p64 -> (function p65 -> (function p66 -> (function p67 -> (function p68 -> (function p69 -> (function p70 -> (function p71 -> (function p72 -> (function p73 -> (function p74 -> (function p75 -> (function p76 -> (function p77 -> (function p78 -> (function p79 -> (function p80 -> (function p81 -> (function p82 -> (function p83 -> (function p84 -> (function p85 -> (function p86 -> (function p87 -> (function p88 -> (function p89 -> (function p90 -> (function o -> 
(match o with 
   ADC -> p
 | ADD -> p1
 | AIS -> p2
 | AIX -> p3
 | AND -> p4
 | ASL -> p5
 | ASR -> p6
 | BCC -> p7
 | BCLRn -> p8
 | BCS -> p9
 | BEQ -> p10
 | BGE -> p11
 | BGND -> p12
 | BGT -> p13
 | BHCC -> p14
 | BHCS -> p15
 | BHI -> p16
 | BIH -> p17
 | BIL -> p18
 | BIT -> p19
 | BLE -> p20
 | BLS -> p21
 | BLT -> p22
 | BMC -> p23
 | BMI -> p24
 | BMS -> p25
 | BNE -> p26
 | BPL -> p27
 | BRA -> p28
 | BRCLRn -> p29
 | BRN -> p30
 | BRSETn -> p31
 | BSETn -> p32
 | BSR -> p33
 | CBEQA -> p34
 | CBEQX -> p35
 | CLC -> p36
 | CLI -> p37
 | CLR -> p38
 | CMP -> p39
 | COM -> p40
 | CPHX -> p41
 | CPX -> p42
 | DAA -> p43
 | DBNZ -> p44
 | DEC -> p45
 | DIV -> p46
 | EOR -> p47
 | INC -> p48
 | JMP -> p49
 | JSR -> p50
 | LDA -> p51
 | LDHX -> p52
 | LDX -> p53
 | LSR -> p54
 | MOV -> p55
 | MUL -> p56
 | NEG -> p57
 | NOP -> p58
 | NSA -> p59
 | ORA -> p60
 | PSHA -> p61
 | PSHH -> p62
 | PSHX -> p63
 | PULA -> p64
 | PULH -> p65
 | PULX -> p66
 | ROL -> p67
 | ROR -> p68
 | RSP -> p69
 | RTI -> p70
 | RTS -> p71
 | SBC -> p72
 | SEC -> p73
 | SEI -> p74
 | SHA -> p75
 | SLA -> p76
 | STA -> p77
 | STHX -> p78
 | STOP -> p79
 | STX -> p80
 | SUB -> p81
 | SWI -> p82
 | TAP -> p83
 | TAX -> p84
 | TPA -> p85
 | TST -> p86
 | TSX -> p87
 | TXA -> p88
 | TXS -> p89
 | WAIT -> p90)
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
;;

let opcode_rect =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function p5 -> (function p6 -> (function p7 -> (function p8 -> (function p9 -> (function p10 -> (function p11 -> (function p12 -> (function p13 -> (function p14 -> (function p15 -> (function p16 -> (function p17 -> (function p18 -> (function p19 -> (function p20 -> (function p21 -> (function p22 -> (function p23 -> (function p24 -> (function p25 -> (function p26 -> (function p27 -> (function p28 -> (function p29 -> (function p30 -> (function p31 -> (function p32 -> (function p33 -> (function p34 -> (function p35 -> (function p36 -> (function p37 -> (function p38 -> (function p39 -> (function p40 -> (function p41 -> (function p42 -> (function p43 -> (function p44 -> (function p45 -> (function p46 -> (function p47 -> (function p48 -> (function p49 -> (function p50 -> (function p51 -> (function p52 -> (function p53 -> (function p54 -> (function p55 -> (function p56 -> (function p57 -> (function p58 -> (function p59 -> (function p60 -> (function p61 -> (function p62 -> (function p63 -> (function p64 -> (function p65 -> (function p66 -> (function p67 -> (function p68 -> (function p69 -> (function p70 -> (function p71 -> (function p72 -> (function p73 -> (function p74 -> (function p75 -> (function p76 -> (function p77 -> (function p78 -> (function p79 -> (function p80 -> (function p81 -> (function p82 -> (function p83 -> (function p84 -> (function p85 -> (function p86 -> (function p87 -> (function p88 -> (function p89 -> (function p90 -> (function o -> 
(match o with 
   ADC -> p
 | ADD -> p1
 | AIS -> p2
 | AIX -> p3
 | AND -> p4
 | ASL -> p5
 | ASR -> p6
 | BCC -> p7
 | BCLRn -> p8
 | BCS -> p9
 | BEQ -> p10
 | BGE -> p11
 | BGND -> p12
 | BGT -> p13
 | BHCC -> p14
 | BHCS -> p15
 | BHI -> p16
 | BIH -> p17
 | BIL -> p18
 | BIT -> p19
 | BLE -> p20
 | BLS -> p21
 | BLT -> p22
 | BMC -> p23
 | BMI -> p24
 | BMS -> p25
 | BNE -> p26
 | BPL -> p27
 | BRA -> p28
 | BRCLRn -> p29
 | BRN -> p30
 | BRSETn -> p31
 | BSETn -> p32
 | BSR -> p33
 | CBEQA -> p34
 | CBEQX -> p35
 | CLC -> p36
 | CLI -> p37
 | CLR -> p38
 | CMP -> p39
 | COM -> p40
 | CPHX -> p41
 | CPX -> p42
 | DAA -> p43
 | DBNZ -> p44
 | DEC -> p45
 | DIV -> p46
 | EOR -> p47
 | INC -> p48
 | JMP -> p49
 | JSR -> p50
 | LDA -> p51
 | LDHX -> p52
 | LDX -> p53
 | LSR -> p54
 | MOV -> p55
 | MUL -> p56
 | NEG -> p57
 | NOP -> p58
 | NSA -> p59
 | ORA -> p60
 | PSHA -> p61
 | PSHH -> p62
 | PSHX -> p63
 | PULA -> p64
 | PULH -> p65
 | PULX -> p66
 | ROL -> p67
 | ROR -> p68
 | RSP -> p69
 | RTI -> p70
 | RTS -> p71
 | SBC -> p72
 | SEC -> p73
 | SEI -> p74
 | SHA -> p75
 | SLA -> p76
 | STA -> p77
 | STHX -> p78
 | STOP -> p79
 | STX -> p80
 | SUB -> p81
 | SWI -> p82
 | TAP -> p83
 | TAX -> p84
 | TPA -> p85
 | TST -> p86
 | TSX -> p87
 | TXA -> p88
 | TXS -> p89
 | WAIT -> p90)
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
;;

type any_opcode =
AnyOP of opcode
;;

let any_opcode_rec =
(function m -> (function f -> (function a -> 
(match a with 
   AnyOP(o) -> (f o))
)))
;;

let any_opcode_rect =
(function m -> (function f -> (function a -> 
(match a with 
   AnyOP(o) -> (f o))
)))
;;

type byte8_or_word16 =
Byte of Matita_freescale_byte8.byte8
 | Word of Matita_freescale_word16.word16
;;

let byte8_or_word16_rec =
(function f -> (function f1 -> (function b -> 
(match b with 
   Byte(b1) -> (f b1)
 | Word(w) -> (f1 w))
)))
;;

let byte8_or_word16_rect =
(function f -> (function f1 -> (function b -> 
(match b with 
   Byte(b1) -> (f b1)
 | Word(w) -> (f1 w))
)))
;;

let byte8_or_word16_OF_bitrigesim =
(function a -> (Byte((Matita_freescale_aux_bases.byte8_of_bitrigesim a))))
;;

let magic_of_opcode =
(function o -> 
(match o with 
   ADC -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | ADD -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))
 | AIS -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))
 | AIX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))
 | AND -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))
 | ASL -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))
 | ASR -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))
 | BCC -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X7))
 | BCLRn -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))
 | BCS -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))
 | BEQ -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))
 | BGE -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XB))
 | BGND -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC))
 | BGT -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD))
 | BHCC -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))
 | BHCS -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))
 | BHI -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))
 | BIH -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X1))
 | BIL -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X2))
 | BIT -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X3))
 | BLE -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X4))
 | BLS -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X5))
 | BLT -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X6))
 | BMC -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X7))
 | BMI -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8))
 | BMS -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9))
 | BNE -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA))
 | BPL -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XB))
 | BRA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC))
 | BRCLRn -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XD))
 | BRN -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XE))
 | BRSETn -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XF))
 | BSETn -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X0))
 | BSR -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X1))
 | CBEQA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X2))
 | CBEQX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X3))
 | CLC -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X4))
 | CLI -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X5))
 | CLR -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X6))
 | CMP -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X7))
 | COM -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X8))
 | CPHX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X9))
 | CPX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XA))
 | DAA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XB))
 | DBNZ -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XC))
 | DEC -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XD))
 | DIV -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XE))
 | EOR -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XF))
 | INC -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X0))
 | JMP -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X1))
 | JSR -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X2))
 | LDA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X3))
 | LDHX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X4))
 | LDX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X5))
 | LSR -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X6))
 | MOV -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X7))
 | MUL -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X8))
 | NEG -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X9))
 | NOP -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XA))
 | NSA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XB))
 | ORA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XC))
 | PSHA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XD))
 | PSHH -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XE))
 | PSHX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XF))
 | PULA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X0))
 | PULH -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X1))
 | PULX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X2))
 | ROL -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X3))
 | ROR -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X4))
 | RSP -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X5))
 | RTI -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X6))
 | RTS -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X7))
 | SBC -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X8))
 | SEC -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X9))
 | SEI -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XA))
 | SHA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XB))
 | SLA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XC))
 | STA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XD))
 | STHX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XE))
 | STOP -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XF))
 | STX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X0))
 | SUB -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X1))
 | SWI -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X2))
 | TAP -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X3))
 | TAX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X4))
 | TPA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X5))
 | TST -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X6))
 | TSX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X7))
 | TXA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X8))
 | TXS -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X9))
 | WAIT -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.XA)))
)
;;

let eqop =
(function m -> (function o -> (function o' -> 
(match o with 
   AnyOP(p) -> 
(match o' with 
   AnyOP(p') -> (Matita_freescale_byte8.eq_b8 (magic_of_opcode p) (magic_of_opcode p')))
)
)))
;;

let magic_of_instr_mode =
(function i -> 
(match i with 
   MODE_INH -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | MODE_INHA -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))
 | MODE_INHX -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))
 | MODE_INHH -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))
 | MODE_INHX0ADD -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))
 | MODE_INHX1ADD -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))
 | MODE_INHX2ADD -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))
 | MODE_IMM1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X7))
 | MODE_IMM1EXT -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))
 | MODE_IMM2 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))
 | MODE_DIR1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))
 | MODE_DIR2 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XB))
 | MODE_IX0 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC))
 | MODE_IX1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD))
 | MODE_IX2 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))
 | MODE_SP1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))
 | MODE_SP2 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))
 | MODE_DIR1_to_DIR1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X1))
 | MODE_IMM1_to_DIR1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X2))
 | MODE_IX0p_to_DIR1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X3))
 | MODE_DIR1_to_IX0p -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X4))
 | MODE_INHA_and_IMM1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X5))
 | MODE_INHX_and_IMM1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X6))
 | MODE_IMM1_and_IMM1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X7))
 | MODE_DIR1_and_IMM1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8))
 | MODE_IX0_and_IMM1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9))
 | MODE_IX0p_and_IMM1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA))
 | MODE_IX1_and_IMM1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XB))
 | MODE_IX1p_and_IMM1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC))
 | MODE_SP1_and_IMM1 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XD))
 | MODE_DIRn(o) -> (Matita_freescale_byte8.plus_b8nc (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XE)) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,(Matita_freescale_aux_bases.exadecim_of_oct o))))
 | MODE_DIRn_and_IMM1(o) -> (Matita_freescale_byte8.plus_b8nc (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X6)) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,(Matita_freescale_aux_bases.exadecim_of_oct o))))
 | MODE_TNY(e) -> (Matita_freescale_byte8.plus_b8nc (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XE)) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,e)))
 | MODE_SRT(t) -> (Matita_freescale_byte8.plus_b8nc (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XE)) (Matita_freescale_aux_bases.byte8_of_bitrigesim t)))
)
;;

let eqim =
(function i -> (function i' -> (Matita_freescale_byte8.eq_b8 (magic_of_instr_mode i) (magic_of_instr_mode i'))))
;;

let get_byte_count =
let rec get_byte_count = 
(function m -> (function b -> (function c -> (function l -> 
(match l with 
   Matita_list_list.Nil -> c
 | Matita_list_list.Cons(hd,tl) -> 
(match (Matita_freescale_extra.thd4T hd) with 
   Byte(b') -> 
(match (Matita_freescale_byte8.eq_b8 b b') with 
   Matita_datatypes_bool.True -> (get_byte_count m b (Matita_nat_nat.S(c)) tl)
 | Matita_datatypes_bool.False -> (get_byte_count m b c tl))

 | Word(_) -> (get_byte_count m b c tl))
)
)))) in get_byte_count
;;

let get_word_count =
let rec get_word_count = 
(function m -> (function b -> (function c -> (function l -> 
(match l with 
   Matita_list_list.Nil -> c
 | Matita_list_list.Cons(hd,tl) -> 
(match (Matita_freescale_extra.thd4T hd) with 
   Byte(_) -> (get_word_count m b c tl)
 | Word(w) -> 
(match (Matita_freescale_word16.eq_w16 (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.XE)),b)) w) with 
   Matita_datatypes_bool.True -> (get_word_count m b (Matita_nat_nat.S(c)) tl)
 | Matita_datatypes_bool.False -> (get_word_count m b c tl))
)
)
)))) in get_word_count
;;

let get_pseudo_count =
let rec get_pseudo_count = 
(function m -> (function o -> (function c -> (function l -> 
(match l with 
   Matita_list_list.Nil -> c
 | Matita_list_list.Cons(hd,tl) -> 
(match (Matita_freescale_extra.fst4T hd) with 
   AnyOP(o') -> 
(match (eqop m (AnyOP(o)) (AnyOP(o'))) with 
   Matita_datatypes_bool.True -> (get_pseudo_count m o (Matita_nat_nat.S(c)) tl)
 | Matita_datatypes_bool.False -> (get_pseudo_count m o c tl))
)
)
)))) in get_pseudo_count
;;

let get_mode_count =
let rec get_mode_count = 
(function m -> (function i -> (function c -> (function l -> 
(match l with 
   Matita_list_list.Nil -> c
 | Matita_list_list.Cons(hd,tl) -> 
(match (eqim (Matita_freescale_extra.snd4T hd) i) with 
   Matita_datatypes_bool.True -> (get_mode_count m i (Matita_nat_nat.S(c)) tl)
 | Matita_datatypes_bool.False -> (get_mode_count m i c tl))
)
)))) in get_mode_count
;;

let test_not_impl_byte =
let rec test_not_impl_byte = 
(function b -> (function l -> 
(match l with 
   Matita_list_list.Nil -> Matita_datatypes_bool.False
 | Matita_list_list.Cons(hd,tl) -> 
(match (Matita_freescale_byte8.eq_b8 b hd) with 
   Matita_datatypes_bool.True -> Matita_datatypes_bool.True
 | Matita_datatypes_bool.False -> (test_not_impl_byte b tl))
)
)) in test_not_impl_byte
;;

let test_not_impl_pseudo =
let rec test_not_impl_pseudo = 
(function o -> (function l -> 
(match l with 
   Matita_list_list.Nil -> Matita_datatypes_bool.False
 | Matita_list_list.Cons(hd,tl) -> 
(match (eqop HC05 (AnyOP(o)) (AnyOP(hd))) with 
   Matita_datatypes_bool.True -> Matita_datatypes_bool.True
 | Matita_datatypes_bool.False -> (test_not_impl_pseudo o tl))
)
)) in test_not_impl_pseudo
;;

let test_not_impl_mode =
let rec test_not_impl_mode = 
(function i -> (function l -> 
(match l with 
   Matita_list_list.Nil -> Matita_datatypes_bool.False
 | Matita_list_list.Cons(hd,tl) -> 
(match (eqim i hd) with 
   Matita_datatypes_bool.True -> Matita_datatypes_bool.True
 | Matita_datatypes_bool.False -> (test_not_impl_mode i tl))
)
)) in test_not_impl_mode
;;

let get_OpIm_count =
let rec get_OpIm_count = 
(function m -> (function o -> (function i -> (function c -> (function l -> 
(match l with 
   Matita_list_list.Nil -> c
 | Matita_list_list.Cons(hd,tl) -> 
(match (Matita_freescale_extra.and_bool (eqop m o (Matita_freescale_extra.fst4T hd)) (eqim i (Matita_freescale_extra.snd4T hd))) with 
   Matita_datatypes_bool.True -> (get_OpIm_count m o i (Matita_nat_nat.S(c)) tl)
 | Matita_datatypes_bool.False -> (get_OpIm_count m o i c tl))
)
))))) in get_OpIm_count
;;

let forall_opcode =
(function p -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (p ADC) (p ADD)) (p AIS)) (p AIX)) (p AND)) (p ASL)) (p ASR)) (p BCC)) (p BCLRn)) (p BCS)) (p BEQ)) (p BGE)) (p BGND)) (p BGT)) (p BHCC)) (p BHCS)) (p BHI)) (p BIH)) (p BIL)) (p BIT)) (p BLE)) (p BLS)) (p BLT)) (p BMC)) (p BMI)) (p BMS)) (p BNE)) (p BPL)) (p BRA)) (p BRCLRn)) (p BRN)) (p BRSETn)) (p BSETn)) (p BSR)) (p CBEQA)) (p CBEQX)) (p CLC)) (p CLI)) (p CLR)) (p CMP)) (p COM)) (p CPHX)) (p CPX)) (p DAA)) (p DBNZ)) (p DEC)) (p DIV)) (p EOR)) (p INC)) (p JMP)) (p JSR)) (p LDA)) (p LDHX)) (p LDX)) (p LSR)) (p MOV)) (p MUL)) (p NEG)) (p NOP)) (p NSA)) (p ORA)) (p PSHA)) (p PSHH)) (p PSHX)) (p PULA)) (p PULH)) (p PULX)) (p ROL)) (p ROR)) (p RSP)) (p RTI)) (p RTS)) (p SBC)) (p SEC)) (p SEI)) (p SHA)) (p SLA)) (p STA)) (p STHX)) (p STOP)) (p STX)) (p SUB)) (p SWI)) (p TAP)) (p TAX)) (p TPA)) (p TST)) (p TSX)) (p TXA)) (p TXS)) (p WAIT)))
;;

let forall_instr_mode =
(function p -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (p MODE_INH) (p MODE_INHA)) (p MODE_INHX)) (p MODE_INHH)) (p MODE_INHX0ADD)) (p MODE_INHX1ADD)) (p MODE_INHX2ADD)) (p MODE_IMM1)) (p MODE_IMM1EXT)) (p MODE_IMM2)) (p MODE_DIR1)) (p MODE_DIR2)) (p MODE_IX0)) (p MODE_IX1)) (p MODE_IX2)) (p MODE_SP1)) (p MODE_SP2)) (p MODE_DIR1_to_DIR1)) (p MODE_IMM1_to_DIR1)) (p MODE_IX0p_to_DIR1)) (p MODE_DIR1_to_IX0p)) (p MODE_INHA_and_IMM1)) (p MODE_INHX_and_IMM1)) (p MODE_IMM1_and_IMM1)) (p MODE_DIR1_and_IMM1)) (p MODE_IX0_and_IMM1)) (p MODE_IX0p_and_IMM1)) (p MODE_IX1_and_IMM1)) (p MODE_IX1p_and_IMM1)) (p MODE_SP1_and_IMM1)) (Matita_freescale_aux_bases.forall_oct (function o -> (p (MODE_DIRn(o)))))) (Matita_freescale_aux_bases.forall_oct (function o -> (p (MODE_DIRn_and_IMM1(o)))))) (Matita_freescale_exadecim.forall_exadecim (function e -> (p (MODE_TNY(e)))))) (Matita_freescale_aux_bases.forall_bitrigesim (function t -> (p (MODE_SRT(t)))))))
;;

