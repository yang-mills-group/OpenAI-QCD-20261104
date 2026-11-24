import YM.Massive.PCAC.Smalt
import YM.Massive.PCAC.Mixed
import YM.QCD.Bay.Wharf
/-! Quadratic/harmonic test on same total axial/vector Ward operations in a run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
open scoped Kronecker
open Finset
variable (X Y:Spike)(a b:Flavor F)
local notation "F'"=> flavorW X a b c
local notation "cell"=> QCD.Run.cell -- syntax
abbrev piece (a b:Flavor F)(T:Sour (Modes c F)): Sheet c:= Matrix.of fun i j=> T (i,a) (j,b)
lemma cutsLeft (A:Sour (Modes c F)) : piece a b (F'*A) = onSpin c X * piece b b A:=by
    ext i j; rw [piece, Matrix.of_apply,Matrix.mul_apply,Matrix.mul_apply,Fintype.sum_prod_type]; unfold flavorW spot; simp -- apply diag simp subset
lemma cutsRight (A:Sour (Modes c F)): piece a b (A*F')= piece a a A * onSpin c X:=by
    ext i j; rw [piece,Matrix.of_apply,Matrix.mul_apply,Matrix.mul_apply,Fintype.sum_prod_type]; unfold flavorW spot; simp

abbrev spinTest (Y:Spike)(i j:Site c)(Z:Sheet c):ℂ:= ((cell Z i j)*(Lat.wave Y)).trace
lemma spinLeft (Z:Sheet c)(hY:Y*X=1)(i j: Site c) : spinTest Y i j (onSpin c X*Z) = spinTest 1 i j Z:=by
    unfold spinTest onSpin; rw [Bay.cell_ride_left,Equiv.refl_apply, wave_one,mul_one, show ((wave X*_)*_).trace= _ from ?_]
    rw [Matrix.trace_mul_comm (wave X * cell Z i j), ← mul_assoc, wave_mul, hY,wave_one,one_mul] -- show meta
lemma spinRight (Z:Sheet c)(hY:X*Y=1)(i j:Site c) : spinTest Y i j (Z*onSpin c X) = spinTest 1 i j Z:=by
    have he : onSpin c X=star (rides (Equiv.refl _) (fun _=>wave (star X))) :=by change _=star (onSpin c (star X)); rw [on_spin_star,star_star]
    unfold spinTest; rw [he, Bay.cell_ride_right,Equiv.refl_apply,wave_star,star_star, mul_assoc, wave_mul,hY,wave_one,mul_one]

-- Could state at any spectrum. In this work a specific AP smallest wave pair. Cost denominator: BODY of UNMARKED density at flat, not body of what is probed.
local notation "p"=>Run.plane
noncomputable def horn (X:Spike)(a b:Flavor F)(u:ℂ)(x:Fields c F): ℂ:=
    (∑ i:Site c,∑ j:Site c, star (p i)*spinTest X i j (piece a b (traceP x))*p j) / u / ((Fintype.card (Site c):ℂ) * (Fintype.card Lat.Fiber:ℕ))
lemma point_cost (A:Density c F) (a:Flavor F) : horn (1:Spike) a a (Stiffness.body A 1) (A 1)=
    (∑ i:Site c,∑ j:Site c,∑ u:Lat.Fiber, star (p i)*Run.negQuadratic A ((i,u),a) ((j,u),a)*p j) / ((Fintype.card (Site c):ℂ)*(Fintype.card Lat.Fiber:ℕ)):=by
     unfold horn spinTest; simp_rw [wave_one,mul_one,Matrix.trace,Matrix.diag_apply];
     let x (i j:Site c) (u:Lat.Fiber):= traceP (A 1) ((i,u),a) ((j,u),a); let d:= Stiffness.body A 1
     congr 1; change _ / d= _; rw [sum_div]; apply sum_congr rfl; intro i _; rw [sum_div]; apply sum_congr rfl; intro j _; rw [mul_sum,sum_mul,sum_div]; apply sum_congr rfl; intro k _; change _*x i j k*p j/d= star (p i)*(x i j k/d)*p j; ring
lemma axial_quote (T:Fields c F) (u:ℂ)(hX:X*Y=1)(hY:Y*X=1)(k:Bool): horn Y a b u (applyMark k F' T)= horn 1 (if k then b else a) (if k then b else a) u T:=by
    unfold horn; cases k
    · simp only [Bool.false_eq_true, ↓reduceIte,(Grass.Ward.quote ..), cutsRight, spinRight X Y _ hX]
    simp only [Grass.Ward.quote,↓reduceIte,cutsLeft,spinLeft X Y _ hY]
lemma horn_sub (x y:Fields c F)(u:ℂ): horn X a b u (x-y)=horn X a b u x - horn X a b u y:=by
    have he : traceP (x-y)=traceP x-traceP y:=by ext i j; change _=traceP _ _ _-_; unfold traceP; simp; abel
    unfold horn; rw [he, show piece a b (traceP x-traceP y)= piece a b (traceP x)-piece a b (traceP y) from rfl]; unfold spinTest; simp_rw [show ∀ i j:Site c, cell (piece a b (traceP x)-piece a b (traceP y)) i j= cell (piece a b (traceP x)) i j-cell (piece a b (traceP y)) i j from fun _ _=>rfl, sub_mul, Matrix.trace_sub,mul_sub,sub_mul,sum_sub_distrib,sub_div]
lemma horn_add (x y:Fields c F)(u:ℂ): horn X a b u (x+y)=horn X a b u x+horn X a b u y:=by apply sub_eq_iff_eq_add.mp; rw [← horn_sub,add_sub_cancel_right]
variable {R:Side}{S:Scheme}(T:Run S N R F)
noncomputable def chord (i:ℕ)(U:Insertion (S.side R i) F):= horn X a b (Stiffness.body (T.density i) 1) (U 1)
lemma answering (k:Bool)(hX:X*Y=1)(hY:Y*X=1)(i:ℕ)(hi:i≤N)(ht:T.Actual): chord Y a b T i (film X a b T k i)= T.massRead i (if k then b else a):=by
    unfold chord film mark; rw [stroll_at,(show actor T i 1=T.density i 1 from congr_fun (act T ht hi) 1),axial_quote X Y a b _ _ hX hY k]; exact point_cost ..
lemma chord_sub {i:ℕ}(U V:Insertion (S.side R i) F) : chord X a b T i (U-V)=chord X a b T i U-chord X a b T i V:=horn_sub ..
lemma chord_add {i:ℕ}(U V:Insertion (S.side R i) F) : chord X a b T i (U+V)=chord X a b T i U+chord X a b T i V:= horn_add ..
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.answering
