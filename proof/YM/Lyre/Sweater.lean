import YM.Lyre.Mirage
/-! Uniform two-sided seam estimate using ETH at *only endpoints*. Fits average sensors by aligned seam choices (no costs at unaligned smear shifts). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix ComplexOrder
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead QCD.Revolve Tide Plum
open TorusPCAC.Geometry Chess Patria Patria.Exposure Cells QCD.RP
variable {i j k d N n r t m:ℕ}{c f:Side}
open Romance.HankV (steeper tideV steepP sunkP)
-- real convex bound endpoints
lemma endPlot (B:ℝ)(U:ℕ→ℝ)(h:U 0≤B)(he:U n≤B) (hv:∀ i,i+2≤ n→ U (i+1)-U i≤ U (i+2)-U (i+1)) (i:ℕ)(hp:i≤n): U i≤B:=by
    rcases hp.eq_or_lt with hp|hp; rw [hp]; exact he
    by_contra! hx; have hu:0< i:= Nat.pos_of_ne_zero (fun e=> (not_le_of_gt hx) (e ▸ h))
    have hi:U i-U 0≤ i*(U (i+1)-U i):=by simpa using sunkP U hv (show 0+i≤ i by omega) hp
    have hD : U i< U (i+1):=by
      have hP:0 < (i:ℝ)*(U (i+1)-U i):=by linarith only [hi,hx,h]
      exact sub_pos.mp (pos_of_mul_pos_right hP (show 0≤(i:ℝ) from by positivity))
    obtain ⟨s,hs⟩:= Nat.exists_eq_add_of_le hp.le; have hy:= steepP U hv (show i+s≤ n from hs ▸ le_rfl); rw [←hs] at hy; exact (not_le_of_gt hx) ((sub_nonneg.mp (le_trans (mul_nonneg (by positivity) (sub_nonneg.mpr hD.le)) hy)).trans he)
variable (C: Regulator c 6) (T: Cells.Cut c)
variable (a:Cover)(x y:Stud c 6)
local notation "Q"=>T.sector
local notation "θ"=> tallH T
local notation "R"=>valueH C
local notation "K"=> meritX C T
local notation "ρ" i:arg => depthM a x i
local notation "η" i:arg=> depthM a y i
variable (h:C.t=0) (hL:T.kind=.link)(hh:2 ≤ T.half.val)(hu: 0 ≤ C.β)(he:0<C.Z) (ha:T.flip.act a= -a)
structure Cozy (x:Stud c 6)(n:ℕ)(B:ℝ): Prop where
     roof i:i≤n→Fence T.sector (depthM a x i)
     left: ‖meritX C T (depthM a x 0) (depthM a x 0)‖ ≤ B
     right: ‖meritX C T (depthM a x n) (depthM a x n)‖ ≤ B
variable {B D:ℝ}(hx:Cozy C T a x n B)(hy:Cozy C T a y n B)
include h hL hh hu he ha hx
lemma bounded(i:ℕ)(hi:i≤n) : 0 ≤ bodyF C T a x i ∧ ‖K (ρ i) (ρ i)‖ ≤ B:=by
    let F:= bodyF C T a x; have he'(i:ℕ)(hi:i≤n):0 ≤ F i ∧ ‖K (ρ i) (ρ i)‖= F i:= (spends C T h hL hh hu he _ (hx.roof i hi)).2
    have hp:= he' i hi; refine ⟨hp.1,hp.2.le.trans ?_⟩; exact endPlot B F ((he' 0 (Nat.zero_le _)).2.symm.le.trans hx.left) ((he' _ le_rfl).2.symm.le.trans hx.right) (fun i h'=> stroll C T a x h hL hh hu he ha hx.roof h') i hi
lemma charged (i j k:ℕ)(hK:1≤k)(hv:k ≤ i)(hm:i+j+k ≤ n) : ‖K x (ρ (2*(i+j)))-K x (ρ (2*i))‖ ≤ (j:ℝ)*(B/(k:ℝ)):=by
    let f:= bodyF C T a x
    have hp :Stays x:=by have hx:= (hx.roof 0 (Nat.zero_le _)).hp; unfold depthM at hx; rw [zero_smul,march0] at hx; exact hx
    have hi (i:ℕ) (ht':i≤n):0 ≤ f i ∧ K x (ρ (2*i))= (↑(f i):ℂ) ∧ f i ≤ B:=by
         obtain ⟨H,h1,h2⟩:= spends C T h hL hh hu he _ (hx.roof i ht'); obtain ⟨hb,h'⟩:=bounded C T a x h hL hh hu he ha hx i ht'; exact ⟨hb,by rw [two_mul,← bothM C T a x x hp hp h hL ha]; exact H,h2.symm.le.trans h' ⟩
    rw [(hi _ (by omega :i+j≤n)).2.1,(hi _ (by omega: i≤n)).2.1,← Complex.ofReal_sub, Complex.norm_real,Real.norm_eq_abs]
    exact steeper _ (fun i hi'=> (hi i hi').1) (fun i hi'=> (hi i hi').2.2) (fun i hi' => stroll C T a x h hL hh hu he ha hx.roof hi') hK hv hm
include hy
lemma sum_cozy (g:ℂ)(hg:‖g‖=1):Cozy C T a (x+g • y) n (4*B):=by
    have hp(i:ℕ)(hi:i≤n) : ‖K (depthM a (x+g • y) i) (depthM a (x+g • y) i)‖ ≤ 4*B:=by
       let p:=ρ i; let q:=η i
       have hXX: Fence T.sector p:= hx.roof i hi; have hY:Fence T.sector q :=hy.roof _ hi
       have hp:‖K p p‖ ≤ B:=(bounded C T a x h hL hh hu he ha hx i hi).2; have hq: ‖K q q‖ ≤ B:=(bounded C T a y h hL hh hu he ha hy i hi).2; have ht:0 ≤ B:=(norm_nonneg _).trans hp
       have hm(x y:Stud c 6)(H:Fence Q x)(h':Fence Q y)(hx: ‖K x x‖≤ B)(hy:‖K y y‖ ≤ B): ‖K x y‖ ≤ B:=le_of_pow_le_pow_left₀ (show (2:ℕ)≠0 from by norm_num) ht ((costX C T h hL hh hu he _ _ H h').trans ((mul_le_mul hx hy (norm_nonneg _) ht).trans_eq (pow_two _).symm)) -- sig
       have hL: ‖star g‖=1:= (norm_star ..).trans hg
       rw [growM,relax C T p q _ _ g hXX.hp hY.hp hXX.hp hY.hp];
       set q1:=g*K p q; set q2:=star g*K q p; set q3:= star g*g*K q q
       have hm1: ‖q1‖ ≤ B:=by rw [show q1=_ from rfl,norm_mul,hg,one_mul]; exact hm _ _ hXX hY hp hq
       have hm2: ‖q2‖ ≤ B:=by rw [show q2=_ from rfl,norm_mul,hL,one_mul]; exact hm _ _ hY hXX hq hp
       have hm3: ‖q3‖ ≤ B:=by rw [show q3=_ from rfl,norm_mul, norm_mul,hg,hL,one_mul,one_mul]; exact hq
       change ‖K p p+q1+q2+q3‖ ≤_; linarith only [hm1,hm2,hm3,hp, norm_add_le (K p p) q1,norm_add_le (K p p+q1) q2, norm_add_le (K p p+q1+q2) q3]
    refine ⟨fun i hi=>?_,hp _ (Nat.zero_le _),hp _ le_rfl⟩; rw [growM]; exact (hx.roof _ hi).add ((hy.roof i hi).mass g)
local notation "tX"=> depthM a
local notation "uK"=> Complex.I
omit ha hL hh hu he h hx hy
lemma sumSign (i:ℕ)(he:Stays x)(hv:Stays y): K x (depthM a y i)=(4:ℂ)⁻¹*((K (x+(1:ℂ) • y) (depthM a (x+(1:ℂ) • y) i)-K (x+(-1:ℂ) • y) (depthM a (x+(-1:ℂ) • y) i)) - uK * (K (x+uK • y) (depthM a (x+uK • y) i)-K (x+ -uK • y) (depthM a (x+ -uK • y) i))):=by
   let f:=K x (ρ i); let p:=K x (η i); let q:=K y (ρ i); let r:=K y (η i)
   have h(c:ℂ): K (x+c • y) (tX (x+c • y) i)= f+c*p+star c*q+ star c*c*r:=by rw [growM]; exact relax C T x y _ _ c he hv (marchP _ x he) (marchP _ y hv)
   rw [h,h,h,h]; simp only [star_one,star_neg, show star uK= -uK from Complex.conj_I]; linear_combination ((f-f)*p+(p-q)/2+0)*Complex.I_sq
include ha hL h hh hu he hx hy
lemma hiker (hK:1≤k)(hv:k ≤ i)(hw:i+j+k ≤ n): ‖K x (η (2*(i+j)))-K x (η (2*i))‖ ≤ (j:ℝ)*(4*B/(k:ℝ)):=by
   let a':=2*(i+j); let b':=2*i; let T' (i:ℕ)(g:ℂ):= K (x+g • y) (depthM a (x+g • y) i); let U(c:ℂ):= T' a' c-T' b' c; let D':=(j:ℝ)*(4*B/(k:ℝ)); have hC: Stays x:=by have H:= (hx.roof 0 (Nat.zero_le _)).hp; unfold depthM at H; rw [zero_smul,march0] at H; exact H
   have hB:Stays y:=by have H:= (hy.roof 0 (Nat.zero_le _)).hp; unfold depthM at H; rw [zero_smul,march0] at H; exact H
   have he(c:ℂ)(h0:‖c‖=1): ‖U c‖ ≤ D':= charged C T a _ h hL hh hu he ha (sum_cozy C T a x y h hL hh hu he ha hx hy c h0) i j k hK hv hw
   have hA:K x (η a') - K x (η b')=(4:ℂ)⁻¹*((U 1-U (-1))-uK*(U uK-U (-uK))):=by rw [sumSign C T a x y a' hC hB,sumSign C T a x y b' hC hB]; unfold U T'; ring
   rw [hA, norm_mul,norm_inv]; let p:= U 1; let q:=U (-1); let r:=U uK; let v:=U (-uK); have hm : ‖p-q-uK*(r-v)‖ ≤ 4*D':=by linarith only [norm_sub_le p q,norm_sub_le r v,norm_sub_le (p-q) (uK*(r-v)), show ‖uK*(r-v)‖=‖r-v‖ from (by simp),show ‖p‖≤D' from he _ (by simp), he (-1) (by simp), he uK (by simp), he (-uK) (by simp)]
   rw [show ‖(4:ℂ)‖=(4:ℝ) by norm_num]; exact (mul_le_mul_of_nonneg_left hm (by norm_num)).trans_eq (by ring)
omit hx hy
-- physical payoff only endcaps; choose b multiple of resolution to fit averaging-calibration
lemma seams (b:ℕ)(hb:1≤b)(hw:d≤ b) :
    let x':= θ x
    let X:= march (-(b • a)) x'; let Y:= march (-(b • a)) y
    Cozy C T a X (4*b) B → Cozy C T a Y (4*b) B → ‖R (x * march ((2*d) • a) y) - R (x*y)‖ ≤ d*(4*B/(b:ℝ)):=by
    intro U X Y hX hY; have hx:Stays X:=by have hx:= (hX.roof 0 (Nat.zero_le _)).hp; unfold depthM at hx; rw[zero_smul,march0] at hx; exact hx
    have hy:Stays Y:=by have hx:= (hY.roof 0 (Nat.zero_le _)).hp; unfold depthM at hx; rw[zero_smul,march0] at hx; exact hx
    have he': depthM a X b=U:=by unfold X depthM; rw [marched,neg_add_cancel,march0]
    have hm: depthM a Y b=y:=by unfold Y depthM; rw [marched,neg_add_cancel,march0]
    have hF(j:ℕ): K X (depthM a Y (b+j))= R (x* depthM a Y j):=by rw [← bothM C T a X Y hx hy h hL ha,he', meritX,tallHy T x] -- hT rewrite U
    have hs: march ((2*d) • a) y=depthM a Y (b+2*d):=by nth_rw 1 [←hm]; unfold depthM; rw [marched,add_smul]
    rw [hs,← hF, show R (x*y)= R (x*depthM a Y b) from (by rw [hm]), ← hF,show b+(b+2*d)= 2*(b+d) from by omega, show b+b=2*b from by omega]; exact hiker C T a X Y h hL hh hu he ha hX hY hb le_rfl (by omega)
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.seams
