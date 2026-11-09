import R6_6_1Rows0
import R6_6_1Rows1
import R6_6_1Rows2
import R6_6_1Rows3
import R6_6_1Rows4
import R6_6_1Rows5
import R6_6_1Rows6
import R6_6_1Rows7
import R6_6_1Rows8
import R6_6_1Rows9
import R6_6_1Rows10
import R6_6_1Rows11
import R6_6_1Rows12
import R6_6_1Rows13
import R6_6_1Rows14
import R6_6_1Rows15
import R6_6_1Rows16
import R6_6_1Rows17
import R6_6_1Rows18
import R6_6_1Rows19
import R6_6_1Rows20
import R6_6_1Rows21
import R6_6_1Rows22
import R6_6_1Rows23
import R6_6_1Rows24
import R6_6_1Rows25
import R6_6_1Rows26
import R6_6_1Rows27
import R6_6_1Rows28
import R6_6_1Rows29
import R6_6_1Rows30
import R6_6_1Rows31
import R6_6_1Rows32
import R6_6_1Rows33
import R6_6_1Rows34
import R6_6_1Rows35
import R6_6_1Rows36
import R6_6_1Rows37
import R6_6_1Rows38
import R6_6_1Rows39
import R6_6_1Rows40
import R6_6_1Rows41
import R6_6_1Rows42
import R6_6_1Rows43
import R6_6_1Rows44
import R6_6_1Rows45
import R6_6_1Rows46
import R6_6_1Rows47
import R6_6_1Rows48
import R6_6_1Rows49
import R6_6_1Rows50
import R6_6_1Rows51
import R6_6_1Rows52
import R6_6_1Rows53
import R6_6_1Rows54
import R6_6_1Rows55
import R6_6_1Rows56
import R6_6_1Rows57
import R6_6_1Rows58
import R6_6_1Rows59
import R6_6_1Rows60
import R6_6_1Rows61
import R6_6_1Rows62
import R6_6_1Rows63
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
def point (i : Fin 24) : GridPoint := (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (1,-1) else (if (i.val-1) < 1 then (2,-2) else (3,-3))) else (if (i.val-3) < 1 then (1,0) else (if ((i.val-3)-1) < 1 then (2,-1) else (3,-2)))) else (if (i.val-6) < 3 then (if (i.val-6) < 1 then (4,-3) else (if ((i.val-6)-1) < 1 then (2,0) else (3,-1))) else (if ((i.val-6)-3) < 1 then (4,-2) else (if (((i.val-6)-3)-1) < 1 then (2,1) else (3,0))))) else (if (i.val-12) < 6 then (if (i.val-12) < 3 then (if (i.val-12) < 1 then (4,-1) else (if ((i.val-12)-1) < 1 then (5,-2) else (3,1))) else (if ((i.val-12)-3) < 1 then (4,0) else (if (((i.val-12)-3)-1) < 1 then (5,-1) else (3,2)))) else (if ((i.val-12)-6) < 3 then (if ((i.val-12)-6) < 1 then (4,1) else (if (((i.val-12)-6)-1) < 1 then (5,0) else (6,-1))) else (if (((i.val-12)-6)-3) < 1 then (4,2) else (if ((((i.val-12)-6)-3)-1) < 1 then (5,1) else (6,0))))))
def group (i : ℕ) : Finset GridPoint := (if i < 6 then (if i < 3 then (if i < 1 then {(1,-1),(5,-1)} else (if (i-1) < 1 then {(2,-2)} else {(3,-3),(3,1)})) else (if (i-3) < 1 then {(1,0),(5,0)} else (if ((i-3)-1) < 1 then {(2,-1),(6,-1)} else {(3,-2),(3,2)}))) else (if (i-6) < 3 then (if (i-6) < 1 then {(4,-3),(4,1)} else (if ((i-6)-1) < 1 then {(2,0),(6,0)} else {(4,-2),(4,2)})) else (if ((i-6)-3) < 1 then {(2,1)} else (if (((i-6)-3)-1) < 1 then {(5,-2)} else {(5,1)}))))
def table (m : ℕ) : ℕ := (if (m/64) < 32 then (if (m/64) < 16 then (if (m/64) < 8 then (if (m/64) < 4 then (if (m/64) < 2 then (if (m/64) < 1 then (rows0 (m-0)) else (rows1 (m-64))) else (if ((m/64)-2) < 1 then (rows2 (m-128)) else (rows3 (m-192)))) else (if ((m/64)-4) < 2 then (if ((m/64)-4) < 1 then (rows4 (m-256)) else (rows5 (m-320))) else (if (((m/64)-4)-2) < 1 then (rows6 (m-384)) else (rows7 (m-448))))) else (if ((m/64)-8) < 4 then (if ((m/64)-8) < 2 then (if ((m/64)-8) < 1 then (rows8 (m-512)) else (rows9 (m-576))) else (if (((m/64)-8)-2) < 1 then (rows10 (m-640)) else (rows11 (m-704)))) else (if (((m/64)-8)-4) < 2 then (if (((m/64)-8)-4) < 1 then (rows12 (m-768)) else (rows13 (m-832))) else (if ((((m/64)-8)-4)-2) < 1 then (rows14 (m-896)) else (rows15 (m-960)))))) else (if ((m/64)-16) < 8 then (if ((m/64)-16) < 4 then (if ((m/64)-16) < 2 then (if ((m/64)-16) < 1 then (rows16 (m-1024)) else (rows17 (m-1088))) else (if (((m/64)-16)-2) < 1 then (rows18 (m-1152)) else (rows19 (m-1216)))) else (if (((m/64)-16)-4) < 2 then (if (((m/64)-16)-4) < 1 then (rows20 (m-1280)) else (rows21 (m-1344))) else (if ((((m/64)-16)-4)-2) < 1 then (rows22 (m-1408)) else (rows23 (m-1472))))) else (if (((m/64)-16)-8) < 4 then (if (((m/64)-16)-8) < 2 then (if (((m/64)-16)-8) < 1 then (rows24 (m-1536)) else (rows25 (m-1600))) else (if ((((m/64)-16)-8)-2) < 1 then (rows26 (m-1664)) else (rows27 (m-1728)))) else (if ((((m/64)-16)-8)-4) < 2 then (if ((((m/64)-16)-8)-4) < 1 then (rows28 (m-1792)) else (rows29 (m-1856))) else (if (((((m/64)-16)-8)-4)-2) < 1 then (rows30 (m-1920)) else (rows31 (m-1984))))))) else (if ((m/64)-32) < 16 then (if ((m/64)-32) < 8 then (if ((m/64)-32) < 4 then (if ((m/64)-32) < 2 then (if ((m/64)-32) < 1 then (rows32 (m-2048)) else (rows33 (m-2112))) else (if (((m/64)-32)-2) < 1 then (rows34 (m-2176)) else (rows35 (m-2240)))) else (if (((m/64)-32)-4) < 2 then (if (((m/64)-32)-4) < 1 then (rows36 (m-2304)) else (rows37 (m-2368))) else (if ((((m/64)-32)-4)-2) < 1 then (rows38 (m-2432)) else (rows39 (m-2496))))) else (if (((m/64)-32)-8) < 4 then (if (((m/64)-32)-8) < 2 then (if (((m/64)-32)-8) < 1 then (rows40 (m-2560)) else (rows41 (m-2624))) else (if ((((m/64)-32)-8)-2) < 1 then (rows42 (m-2688)) else (rows43 (m-2752)))) else (if ((((m/64)-32)-8)-4) < 2 then (if ((((m/64)-32)-8)-4) < 1 then (rows44 (m-2816)) else (rows45 (m-2880))) else (if (((((m/64)-32)-8)-4)-2) < 1 then (rows46 (m-2944)) else (rows47 (m-3008)))))) else (if (((m/64)-32)-16) < 8 then (if (((m/64)-32)-16) < 4 then (if (((m/64)-32)-16) < 2 then (if (((m/64)-32)-16) < 1 then (rows48 (m-3072)) else (rows49 (m-3136))) else (if ((((m/64)-32)-16)-2) < 1 then (rows50 (m-3200)) else (rows51 (m-3264)))) else (if ((((m/64)-32)-16)-4) < 2 then (if ((((m/64)-32)-16)-4) < 1 then (rows52 (m-3328)) else (rows53 (m-3392))) else (if (((((m/64)-32)-16)-4)-2) < 1 then (rows54 (m-3456)) else (rows55 (m-3520))))) else (if ((((m/64)-32)-16)-8) < 4 then (if ((((m/64)-32)-16)-8) < 2 then (if ((((m/64)-32)-16)-8) < 1 then (rows56 (m-3584)) else (rows57 (m-3648))) else (if (((((m/64)-32)-16)-8)-2) < 1 then (rows58 (m-3712)) else (rows59 (m-3776)))) else (if (((((m/64)-32)-16)-8)-4) < 2 then (if (((((m/64)-32)-16)-8)-4) < 1 then (rows60 (m-3840)) else (rows61 (m-3904))) else (if ((((((m/64)-32)-16)-8)-4)-2) < 1 then (rows62 (m-3968)) else (rows63 (m-4032))))))))
def value (A : Finset ℕ) (v : Fin 24) : ℕ := digit (rowOf 12 table A) v.val

end R6_6_1
