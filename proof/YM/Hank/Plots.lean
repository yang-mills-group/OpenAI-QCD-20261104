import YM.Hank.Trans
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix ComplexOrder
namespace Romance.HankV
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead QCD.Revolve Tide
open TorusPCAC.Geometry Chess Patria Patria.Exposure Cells QCD.RP
variable {i j k d N n r t m:ℕ}{c f:Side}
variable (C: Regulator c 6) (T: Cells.Cut c) (a:Cover)
local notation "X"=> Insertion c 6
local notation "Q"=> T.sector
local notation "S"=> banner
local notation "Θ"=> picture T C.zeroCut
local notation "P"=>C.average
abbrev plot (x y:X) := C.average (picture T C.zeroCut x * y)
local notation "L" => plot C T
variable (hq:C.t=0)(hk:T.kind=.link)(ht:0 ≤ C.β)(hp:2≤ T.half.val)(hz:0 < C.Z) (ha:T.flip.act a= -a)
local notation "stepS" i:arg=> banner (i • a)
local notation "uK"=> Complex.I
variable {B D:ℝ}
abbrev Safely (u:X): Prop:= Floors T.sector u ∧ Invariant u
noncomputable abbrev tidal (x:X)(i:ℕ):= banner (i • a) x
local notation "xK"=> tidal a
structure Budget (x:Insertion c 6)(p:ℕ) (B:ℝ) : Prop where
    safe i : i≤p→ Safely T (tidal a x i)
    price i : i≤p→ ‖plot C T (tidal a x i) (tidal a x i)‖ ≤ B
lemma pair_sum (x y:X)(g:ℂ): L (x+g • y) (x+g •y)= L x x+g*L x y+star g*L y x+ star g*g*L y y:=by
   unfold plot; rw [pic_add,pic_smul]; simp only [add_mul,mul_add,mul_smul_comm,smul_mul_assoc,map_add,map_smul,smul_eq_mul]; ring
include ha hq hk
lemma plot_both (j:ℕ)(x y:X): L (xK x j) y = L x (xK y j) :=by
    unfold plot; rw [← letterC C (j • a) (Θ _*_) hq,banner_mul]; rw [show picture _ _ _= banner (-(j • a)) (Θ x) from ?_,order_cast, neg_add_cancel,order0]
    change Θ (banner (j • a) x)=_; rw [exact_stamp C T hq hk]; congr; change T.flip.actEquiv (j • a) = _; rw [map_nsmul, show T.flip.actEquiv a= _ from ha, smul_neg]
lemma plot_add (x y:X)(i j:ℕ):L (xK x i) (xK y j)=L x (xK y (i+j)):=by rw [plot_both C T a hq hk ha]; unfold tidal; rw [order_cast, add_smul,add_comm (j • a)]; -- ordering
omit ha hq
include hz ht hp
lemma precise (x:X)(hx:Safely T x): L x x = ( (L x x).re:ℂ) ∧ 0 ≤ (L x x).re ∧ ‖L x x‖=(L x x).re:=by
   have h:= Regulator.average_reflection hk ht hp hz _ hx.1 hx.2; obtain ⟨hv,hr⟩:= Complex.nonneg_iff.mp h; let X':=L x x; have he:X'= (X'.re:ℂ):=Complex.ext (by simp) (by simpa using hr.symm); exact ⟨he,hv,(congr_arg Norm.norm he).trans (by rw [Complex.norm_real,Real.norm_of_nonneg hv])⟩ -- orientation
lemma between (x y:X)(hx:Safely T x)(hy: Safely T y): ‖L x y‖^2≤ ‖L x x‖*‖L y y‖:=by
   let J (x y:X):= C.raw (Θ x*y); let q:= ‖C.Z⁻¹‖; have he (x y:X): ‖L x y‖=q*‖J x y‖:= norm_smul (C.Z⁻¹:ℂ) (J x y); rw [he,he,he,mul_pow]; refine (mul_le_mul_of_nonneg_left (Regulator.schwarz hk ht hp _ _ hx.1 hy.1 hx.2 hy.2) (sq_nonneg q)).trans_eq ?_; change _= _; dsimp only [J]; ring
lemma join_safe (x y:X)(hx:Safely T x)(hy:Safely T y)(v:ℂ): Safely T (x+v • y):= ⟨flooring_add hx.1 (flooring_smul _ hy.1),invariant_add _ _ hx.2 (invariant_smul _ hy.2 _)⟩
lemma combine (x y:X)(hx:Budget C T a x n B)(hy:Budget C T a y n B)(g:ℂ)(he:‖g‖=1) : Budget C T a (x+g • y) n (4*B):=by
   have hp0(i:ℕ): xK (x+g • y) i=xK x i+g • xK y i:=by rw [tidal,banner_plus,banner_smul];
   constructor
   · intro i hi; rw [hp0]; exact join_safe C T hk ht hp hz _ _ (hx.safe i hi) (hy.safe i hi) g
   intro i hi; let X':=xK x i; let Y:=xK y i
   have hh (x y:X)(hv:Safely T x)(hw: Safely T y)(hx: ‖L x x‖≤ B)(hy:‖L y y‖ ≤ B): ‖L x y‖ ≤ B:=by
        have he:= (between C T hk ht hp hz x y hv hw).trans (mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)); exact le_of_pow_le_pow_left₀ (by norm_num) ((norm_nonneg _).trans hy) (he.trans_eq (pow_two B).symm) -- typo hz arg order.
   rw [hp0,pair_sum]; let F:=L X' Y; let f:=L Y X'; let Pp:=L X' X'; let Qx:=L Y Y; have hg:‖g*F‖=‖F‖:=by rw [norm_mul,he,one_mul];
   have hm:‖star g*f‖= ‖f‖:=by rw [norm_mul,norm_star,he,one_mul]
   have hl:‖star g*g * Qx‖ = ‖Qx‖:=by rw [norm_mul,norm_mul,norm_star,he,one_mul,one_mul]
   have h1 : ‖Pp‖≤B:=hx.price i hi; have h2 : ‖Qx‖≤B:= hy.price i hi; change ‖Pp+_*F+_*f+_*Qx‖ ≤ _; linarith only [hg,hm,hl,h1,h2,norm_add_le (Pp+g*F+star g*f) (star g*g*Qx),norm_add_le (Pp+g*F) (star g*f),norm_add_le Pp (g*F),show ‖F‖≤B from hh _ _ (hx.safe _ hi) (hy.safe _ hi) h1 h2, show ‖f‖≤B from hh _ _ (hy.safe _ hi) (hx.safe _ hi) h2 h1]
omit hk hz ht hp
abbrev fondV (x:X)(i:ℕ):= (plot C T (tidal a x i) (tidal a x i)).re
local notation "Fk"=> fondV C T a
include ha hq hk hz ht hp
lemma connected (x:X)(hx:Budget C T a x n B)(hi:i+2≤n): Fk x (i+1)-Fk x i≤ Fk x (i+2)-Fk x (i+1):=by
   let K(j:ℕ):=xK x j; have he:= between C T hk ht hp hz _ _ (hx.safe i (by omega)) (hx.safe (i+2) hi)
   have h(i:ℕ)(hi:i≤n):0 ≤ Fk x i ∧ ‖L (K i) (K i)‖=Fk x i:=(precise C T hk ht hp hz _ (hx.safe i hi)).2
   have hf:L (K i) (K (i+2))=L (K (i+1)) (K (i+1)):=by unfold K; rw [plot_add C T a hq hk ha,plot_add C T a hq hk ha,show i+(i+2)=i+1+(i+1) by omega]
   rw [hf,(h (i+1) (by omega)).2,(h i (by omega)).2,(h _ hi).2] at he; nlinarith only [sq_nonneg (Fk x i-Fk x (i+2)),he,(h i (by omega)).1,(h _ hi).1,(h (i+1) (by omega)).1] -- need contradiction split
#print axioms plot_add
end HankV
end Romance
end YM.Massive
