import YM.QCD.Plum.Fable

/-!
# `L¹(dU)` control, volume-uniform on all bounded-Borel Grassmann pencils.

Strengthens `Plum.planetary`. Our tests are neutral (local gauge invariant);
no neutrality for flavor or evenly graded condition. Proof adapts the finite
power doubling in `Plum.Belly, Fable`; new step is using *conditional-product*
budget (product under independent Haar, not Gibbs measure), which itself squares
at EVERY doubling and thus preserves the less expensive local prior integral.
Recall project Grass norm is coefficient-sum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Plum.Small
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Tide Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {X:Pixel c F}{J:Patch}{w z:ℝ} {A:Set (Site c)}

/-- This `L¹` is *in addition* to the project `ℓ¹` on Grassmann
coefficients. Works at every step including nonsmooth Borel selectors. -/
noncomputable def bill (x : Stud c F) : ℝ := ∫ i, ‖x i‖ ∂prior su c
noncomputable abbrev Covers (w:ℝ)(x: Stud c F) := bill x ≤ w
lemma bill_nonneg (x:Stud c F) : 0 ≤ bill x := integral_nonneg fun _=> norm_nonneg _
lemma Covers.nonneg {x:Stud c F}(h:Covers w x) : 0 ≤ w := (bill_nonneg x).trans h

private lemma hands (f g:Grid c→ℝ)(S T:Set (Site c))(hs:LocalOn S f)(ht:LocalOn T g)(hf:Stays f)(hg:Stays g)(he:Disjoint S T):
    (∫ U,f U*g U ∂prior su c) = (∫ U,f U ∂prior su c)*(∫ U,g U ∂prior su c):=by
  let p (U:Grid c):ℂ:= f U; let q (U:Grid c):ℂ:=g U
  have hV: Stays p:= hf.flows Complex.continuous_ofReal; have hW:Stays q:=hg.flows Complex.continuous_ofReal
  let m:=su.probHaar; let links:= actualEdges (c:=c)
  have hL:Disjoint (links S) (links T):= Set.disjoint_left.mpr (fun i hi hk=> Set.disjoint_left.1 he (show i.1∈S ∧ _ from hi).1 (show i.1∈T ∧ _ from hk).1)
  have h1(U V:Grid c)(h:Agrees S U V): p U=p V:= congr_arg (↑·:ℝ→ℂ) (hs U V h)
  have h2(U V:Grid c)(h:Agrees T U V): q U=q V:= congr_arg (↑·:ℝ→ℂ) (ht U V h)
  have H:= pi_independent (μ:=su.probHaar) (q:=fun _ _=>1) (read_edges h1) (read_edges h2) hL (by intro i; simp) (fun i=> Envelope.compactC continuous_const) ⟨hV.mes,hV.bounded⟩ ⟨hW.mes,hW.bounded⟩
  simp only [Finset.prod_const_one,one_mul] at H
  unfold p q at H; simp_rw [← Complex.ofReal_mul] at H -- rewrites inner only if RHS coercions
  change (∫ i : Grid c, ↑(f i*g i) ∂prior su c)=(∫ i,(↑(f i):ℂ) ∂prior su c)*(∫ i, ↑(g i) ∂prior su c) at H
  have Hu(f:Grid c→ℝ):(∫ i,(f i:ℂ)∂prior su c)= ((∫ i,f i∂prior su c):ℝ):= integral_ofReal (𝕜:=ℂ)
  rw [Hu (fun i=> f i*g i),Hu f,Hu g,←Complex.ofReal_mul] at H; exact_mod_cast H

/-- No sign estimate on `x` needed, since this step is entirely at prior measure. -/
lemma across {x y: Stud c F} {S T:Set (Site c)}(H:Fence S x)(W:Fence T y)(he:Disjoint S T): bill (x*y) ≤ bill x * bill y:=by
  let p (U:Grid c):= ‖x U‖; let q (U:Grid c):= ‖y U‖
  have hp:Stays p:= H.hp.flows continuous_norm; have hq: Stays q:= W.hp.flows continuous_norm
  unfold bill; apply (integral_mono (((H.hp.mult W.hp).intg (prior su c)).norm) ((hp.mult hq).intg _) (fun U=> (show _ ≤ p U*q U from norm_mul_le ..))).trans_eq
  exact hands p q S T (fun U V h=> congr_arg norm (H.he.1 U V h)) (fun U V h=> congr_arg norm (W.he.1 U V h)) hp hq he

lemma bill_tall (x:Stud c F) (H:Stays x): bill (tallH R x) ≤ bill x:=by
    let p(U:Grid c):ℝ:= ‖x U‖
    have hm: MeasurePreserving (R.pullC su) (prior su c) (prior su c):=prior_pull ..
    have he: Stays p:=H.flows continuous_norm
    let μ:=prior su c; change (∫ i, ‖tallH R x i‖ ∂μ) ≤ ∫ i,p i ∂μ
    have hf(i:Grid c): ‖tallH R x i‖ ≤ p (R.pullC su i):= (roll_fields _ _).trans ((thin _).trans (roll_fields _ _))
    apply (integral_mono (((tallCost x H).intg μ).norm) ((he.travel hm.measurable).intg μ) hf).trans_eq
    have h:=integral_map (μ:=μ) hm.aemeasurable (f:=p) (by rw [show μ.map _=μ from hm.map_eq]; exact (he.intg μ).aestronglyMeasurable); rw [show μ.map _=μ from hm.map_eq] at h; exact h.symm
lemma bill_square (x:Stud c F) (H:Fence (eaves R (longM J)) x)(hr:R.kind=.link) (hx:Covers w x): Covers (w^2) (tallH R x*x):=by
    let Y:=eaves R (longM J); let V:= R.reflect '' Y
    have he: Disjoint V Y:= Set.disjoint_left.mpr (by rintro i ⟨x,hx,rfl⟩ h; exact R.link_switch hr (eaveH _ hr hx) (eaveH _ hr h))
    exact (across (H.tall (Set.mapsTo_image ..)) H he).trans ((mul_le_mul ((bill_tall x H.hp).trans hx) hx (bill_nonneg _) hx.nonneg).trans_eq (pow_two w).symm)

variable (hp:Healing J X)(he:Continuous X)(hv:Cvol X=1)(h: Even c.val)(hN:4≤c.val)
local notation "d"=> longM J
include hp he hv h hN
lemma branchy (p : Site c) (a : Axis) (i : Axis → ℕ) (hi : 2*(i a+2*d) ≤ c.val) (x:Stud c F) (H:Fence (RP.square p i) x) (hA:Covers w x): ∃ q y, Fence (RP.square q (Function.update i a (2*(i a+d)))) y ∧ Covers (F:=F) (w^2) y ∧ ‖Tide.fresh X x‖^2 ≤ ‖Tide.fresh X y‖:=by
    obtain ⟨m,hm⟩:= h; let r:= i a; let R : Cells.Cut c:= ⟨⟨m,by omega⟩,by dsimp; omega, .link,a,p a-(d:Per c)⟩; let j:= update i a (2*(r+d)); let q:=Function.update p a (p a- (↑(r+2*d):Per c)); have hr:2*(r+2*d)≤c.val:=hi
    have ha: RP.square p i⊆eaves R d:=by
         intro x hx; have ht: (x a-p a).val<r:=hx a; have hx:R.distance x=(x a-p a).val+d:=by unfold Cells.Cut.distance; change (x a-(p a- (d:Per c))).val=_; rw [show x a- (p a-(d:Per c))=(↑((x a-p a).val+d):Per c) from (by rw [Nat.cast_add,ZMod.natCast_zmod_val]; abel),ZMod.val_natCast_of_lt (by omega)]
         change d≤_∧_ < m; rw [hx]; omega
    have hY : RP.square p i ⊆ RP.square q j:=by
         intro x hx s; by_cases e:s=a
         · subst s; have ht: (x a-p a).val<r:=hx a; simp only [q,j,update_self]; rw [show x a-(p a- (↑(r+2*d):Per c))=(↑((x a-p a).val+(r+2*d)):Per c) from (by simp only [Nat.cast_add, ZMod.natCast_zmod_val]; abel), ZMod.val_natCast_of_lt (by omega)]; omega
         unfold j q; rw [update_of_ne e,update_of_ne e]; exact hx s
    have hg : Set.MapsTo R.reflect (RP.square p i) (RP.square q j):=by
         intro x hx s; by_cases e:s=a
         · subst s; let b:=(x a-p a).val; have he:b<r:= hx a; have hx:R.reflect x a=2*(p a-(d:Per c))-1-x a:=by simpa only [R,Cells.Kind.shift,Nat.cast_one] using (R.reflect_here x)
           simp only [q,j,update_self,hx]; rw [show 2* (p a-(d:Per c))-1-x a - (p a- (↑(r+2*d):Per c))=(↑(r-(b+1)):Per c) from (by rw [Nat.cast_sub (by omega),Nat.cast_add, Nat.cast_add,show (b:Per c)=x a-p a from ZMod.natCast_zmod_val _]; push_cast; ring), ZMod.val_natCast_of_lt (by omega)]; omega
         unfold j q; rw [R.reflect_there x (show s ≠ R.pos from e),update_of_ne e,update_of_ne e]; exact hx s
    refine ⟨q,tallH R x*x,(H.tall hg).mult (H.high hY), bill_square x (H.high ha) rfl hA,?_⟩; have hb := sheen hp he Fence.one (H.high ha) (show R.kind=.link from rfl) (by change 2 ≤ m; omega); simpa only [tall1,one_mul,fresh1,hv,norm_one] using hb
lemma grows (t :ℕ)(p:Site c)(a:Axis)(i:Axis→ℕ)(hi: 2^t*(i a+2*d) ≤ c.val)(x: Stud c F)(H:Fence (RP.square p i) x)(hx:Covers w x):∃ q y,Fence (RP.square q (Function.update i a (2^t*(i a+2*d)-2*d))) y ∧ Covers (F:=F) (w^(2^t:ℕ)) y∧ ‖Tide.fresh X x‖^(2^t:ℕ) ≤ ‖Tide.fresh X y‖:=by
    induction t with
    | zero=> exact ⟨p,x,by simpa only [pow_zero,one_mul,Nat.add_sub_cancel,Function.update_eq_self] using H,by simpa using hx,by simp⟩
    | succ t ih=>
       rw [pow_succ',mul_assoc] at hi; obtain ⟨q,y,Y,hy,hh⟩:= ih (by omega); let r:=i a; let j:= update i a (2^t*(i a+2*d)-2*d); have het: 2*d ≤2^t*(i a+2*d):= (show 2*d ≤ i a+2*d by omega).trans (le_mul_of_one_le_left (by omega) (show 1 ≤(2:ℕ)^t from one_le_pow₀ (by omega)));
       have hk:j a+2*d=2^t*(i a+2*d):=by unfold j; rw [update_self]; omega
       obtain ⟨s,z,Z,hZ,hQ⟩:= branchy hp he hv h hN q a j (by rw [hk]; exact hi) y Y hy -- he shadow
       refine ⟨s,z,?_,by simpa only [pow_succ (2:ℕ) t, pow_mul] using hZ,?_⟩
       · rw [show 2^(t+1) * (i a+2*d)-2*d=2*(j a+d) from (by rw [pow_succ',mul_assoc,← hk]; omega), show Function.update i a (2*(j a+d))=Function.update j a (2*(j a+d)) from (update_idem ..).symm]; exact Z
       rw [pow_succ,pow_mul]; exact (pow_le_pow_left₀ (by positivity) hh _).trans hQ

omit he hp hv h hN in
lemma sheer (ŝ:ℝ)(hZ:∀ U,‖X U‖ ≤ ŝ)(x:Stud c F)(H:Stays x)(hx:Covers w x): ‖Tide.fresh X x‖ ≤ ŝ*w:=by
    let μ:=prior su c; unfold Tide.fresh
    have ht:0≤ŝ:= (norm_nonneg _).trans (hZ 1)
    apply (norm_integral_le_of_norm_le (μ:=μ) (g:=fun i=> ŝ*‖x i‖) (((H.intg μ).norm).const_mul _) (Eventually.of_forall fun i=>?_)).trans
    rotate_left
    · exact (Grass.price _).trans ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (hZ i) (norm_nonneg _)))
    rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hx ht

variable {t r:ℕ}
include hp hv hN h
lemma quadrant (hY: 2^t*(r+2*d)≤c.val)(p:Site c)(x:Stud c F)(H:Fence (RP.square p fun _=>r) x)(hx:Covers w x):∃ y:Stud c F, Stays y∧Covers (w^((2^t)^4:ℕ)) y ∧ ‖Tide.fresh X x‖^((2^t)^4:ℕ) ≤ ‖Tide.fresh X y‖:=by
    let g (s : Finset Axis) (i : Axis) := if i∈s then 2^t*(r+2*d)-2*d else r
    have Hq (s : Finset Axis) : ∃ (q : Site c) (y : Stud c F), Fence (RP.square q (g s)) y ∧ Covers (w^((2^t)^s.card:ℕ)) y ∧ ‖Tide.fresh X x‖^((2^t)^s.card:ℕ) ≤ ‖Tide.fresh X y‖ := by
        induction s using Finset.induction_on with
        | empty => exact ⟨p,x,by simpa [g] using H,by simpa using hx,by simp⟩
        | @insert a s h₁ ih=>
           obtain ⟨q,y,Y,hy,hQ⟩:= ih; have hi: g s a=r:=by simp [g,h₁]
           obtain ⟨u,z,Z,hz',hg⟩:= grows hp he hv h hN t q a (g s) (by simpa only [hi] using hY) y Y hy -- hY?
           rw [hi,show Function.update (g s) a (2^t*(r+2*d)-2*d)=g (insert a s) from funext fun i=> by rcases eq_or_ne i a with h|h <;> simp [g,h]] at Z; rw [card_insert_of_notMem h₁,pow_succ,pow_mul,pow_mul]; exact ⟨u,z,Z,hz', (pow_le_pow_left₀ (by positivity) hQ _).trans hg⟩
    obtain ⟨u,y,Y,hy,hh⟩:=Hq univ; exact ⟨y,Y.hp,by simpa [Axis] using hy,by simpa [Axis] using hh⟩
/-- Power-of-two chess estimate uniform in volume against one normalized
pixel with link positivity (wide margins) and pressure budget.
The cylinder cost paid is Haar integral, not maximum. -/
lemma planetary (p:Site c)(he':r+2*d ≤ c.val) (x:Stud c F)(H:Fence (RP.square p fun _=>r) x)(hx:Covers w x)(A:ℝ)(hU:∀ U, ‖X U‖ ≤ Globe.expo A c) : ‖Tide.fresh X x‖ ≤ quota J r A * w:=by
    let Q:= r+2*d; have hQ:0<Q:=by unfold Q; change 0<r+2*(40*(J.J+3)); omega
    obtain ⟨m,hM,hk⟩:∃ m:ℕ,2^m*Q ≤ c.val ∧ c.val< 2^(m+1)*Q:=by
        let m:= Nat.log 2 (c.val / Q)
        have hp:2^m ≤ c.val / Q:=Nat.pow_log_le_self 2 (by have hv:c.val / Q ≥ 1:= (Nat.le_div_iff_mul_le hQ).2 (by simpa using he'); omega)
        refine ⟨m,(Nat.le_div_iff_mul_le hQ).1 hp,?_⟩; by_contra! he; exact Nat.not_lt_of_ge ((Nat.le_div_iff_mul_le hQ).2 he) (Nat.lt_pow_succ_log_self (by norm_num) _)
    obtain ⟨y,Y,hw,hY⟩:= quadrant hp he hv h hN hM p x H hx
    have hx':0≤ w:= hx.nonneg; apply le_of_pow_le_pow_left₀ (show ((2^m)^4:ℕ) ≠ 0 by positivity) (mul_nonneg (Real.exp_pos _).le hx'); apply (hY.trans (sheer _ hU y Y hw)).trans; rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (by positivity); unfold Globe.expo; rw [← Real.exp_nat_mul,Real.exp_le_exp,site_card];
    have he : (c.val:ℝ) ≤ (2:ℝ)^m * ↑(2*Q) := by rw [pow_succ, mul_assoc] at hk; exact_mod_cast hk.le
    change -(↑(c.val^4):ℝ)*A ≤ ↑((2^m)^4:ℕ)*(|A| * (↑(2*Q):ℝ)^4); have hp:= pow_le_pow_left₀ (Nat.cast_nonneg _) he 4; rw [mul_pow] at hp; push_cast at *; nlinarith only [mul_le_mul_of_nonneg_left (neg_le_abs A) (show 0≤ (c.val:ℝ)^4 by positivity),mul_le_mul_of_nonneg_right hp (abs_nonneg A)]
end YM.QCD.Plum.Small
#print axioms YM.QCD.Plum.Small.planetary
