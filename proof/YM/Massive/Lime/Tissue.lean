import YM.Massive.Lime.Euler
import YM.QCD.Stew.Stocks

/-! # Woven prices for the log chart

Given an E entry with small price treat exp/log on the mask itself under a
commutative operator norm `Sen`, keeping true sup price of this spin
polynomial in that norm. The (much weaker) full volume-norm comparison is
used only to establish smoothness. Threshold and period-independent.
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lime
open Function Filter Lattice Wilson RG Source Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open Cove Send Stew
open Push.Local
variable {G : Gauge}{n p : Side}{N:ℕ}{t w:ℝ}{o:Site p}
lemma sen_add (x y:EvenA p N) (o:Site p) (t:ℝ) : Sen o t (x+y)≤ Sen o t x+ Sen o t y:=by
  rw [← measures,map_add]; exact norm_add_le ..
lemma sen_mul (h:0≤t)(x y:EvenA p N): Sen o t (x*y)≤ Sen o t x * Sen o t y:= roams (lens o) h x.val y.val
set_option maxHeartbeats 600000 in
theorem left_mul_sen (μ:Site p) (t:ℝ) (ht:0≤t) {D : Directions G n → Prop} {f g : Config G n → EvenA p N} {k : ℕ} {U : Config G n}
    {a b : ℝ} (hf : Chart k f U) (hg : Chart k g U)
    (hc : ∀ l : List (Directions G n), l.length ≤ k → (∀ v∈l, D v) → Sen μ t (leftDerivs f l U) ≤ a)
    (hc' : ∀ l : List (Directions G n), l.length ≤ k → (∀ v∈l, D v) → Sen μ t (leftDerivs g l U) ≤ b) :
    ∀ l : List (Directions G n), l.length ≤ k → (∀ v∈l, D v) → Sen μ t (leftDerivs (f*g) l U) ≤ 2^l.length * (a*b) := by
  intro l hl hD
  induction l using List.reverseRecOn generalizing f g k with
  | nil => simpa [leftDerivs] using (sen_mul ht (f U) (g U)).trans (mul_le_mul
      (hc [] hl hD) (hc' [] hl hD) ((norm_nonneg _)) (((norm_nonneg _)).trans (hc [] hl hD)))
  | append_singleton l A ih =>
    have he : l.length+1 ≤ k := by simpa using hl
    have H (w : Config G n → EvenA p N) (hw : Chart k w U) : Chart l.length (leftDerivs w [A]) U :=
      leftDerivs_chart _ l.length (hw.of_le (Nat.cast_le.mpr (Nat.add_comm .. ▸ he)))
    have hN (w : Config G n → EvenA p N) (c : ℝ) (hw : ∀ l : List (Directions G n), l.length ≤ k → (∀ v∈l, D v) → Sen μ t (leftDerivs w l U) ≤ c)
        (l' : List (Directions G n)) (hl' : l'.length ≤ l.length) (he' : ∀ v∈l', D v) :
        Sen μ t (leftDerivs (leftDerivs w [A]) l' U) ≤ c := by
      rw [← Work.G07.left_append]; refine hw _ (by simp; omega) ?_
      intro v hv; rcases List.mem_append.mp hv with h|h
      · exact he' _ h
      · exact hD _ (List.mem_append_right _ h)
    have ht : leftDerivs (f*g) [A] ∘ increment U =ᶠ[𝓝 0]
        (leftDerivs f [A]*g + f*leftDerivs g [A]) ∘ increment U := by
      have hk : (1:ℕ) ≤ k := by omega
      have h' (w : Config G n → EvenA p N) (hw : Chart k w U) : ∀ᶠ x in 𝓝 0, Chart 1 w (increment U x) :=
        chart_eventually (by rw [Work.G07.at_zero_increment]; exact hw.of_le (Nat.cast_le.mpr hk))
          fun i => by
            simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt
      filter_upwards [h' f hf,h' g hg] with t ht ht'; exact left_first_mul A ht ht'
    rw [Work.G07.left_append,left_congr l U ht]
    have hle : l.length ≤ k := by omega
    have hsf := hf.of_le (Nat.cast_le.mpr hle)
    have hsg := hg.of_le (Nat.cast_le.mpr hle)
    have hd : ∀ v∈l, D v := fun v hv => hD v (by simp [hv])
    rw [left_add l ((H f hf).mul hsg) (hsf.mul (H g hg)) (le_refl l.length)]
    apply (sen_add ..).trans
    exact (add_le_add
      (ih (k:=l.length) (H _ hf) hsg (hN _ a hc) (fun i hi => hc' i (hi.trans hle)) le_rfl hd)
      (ih (k:=l.length) hsf (H _ hg) (fun i hi => hc i (hi.trans hle)) (hN _ b hc') le_rfl hd)).trans_eq (by simp; ring)
open Lat
open Loom Fleet Territory
variable (w:ℝ) (t:ℝ) (x:EvenA p N)
lemma sen_nonneg : 0 ≤ Sen o t x:=norm_nonneg _
lemma sen_neg : Sen o t (-x)= Sen o t x:=by rw [← measures,map_neg,norm_neg]; rfl
lemma sen_real : Sen o t (w • x)= ‖w‖ * Sen o t x:=by
    let v:= (needle o N t).restrictScalars ℝ
    change ‖v (w • x)‖=‖w‖ * ‖v x‖; rw [map_smul,norm_smul]
lemma sen_pow (h:0≤t)(n:ℕ) : Sen o t (x^n) ≤ Sen o t x ^ n:=by
    induction n with
    | zero=>rw [pow_zero,pow_zero]; unfold Sen; rw [show (1:EvenA p N).val= Grass.mono ∅ from Grass.mono_empty.symm]; unfold Stew.plank; rw [sturdy _ _ h]; simp [starch,pieD]
    | succ n ih=> rw [pow_succ,pow_succ]; exact (sen_mul h ..).trans (mul_le_mul_of_nonneg_right ih (sen_nonneg ..))
lemma sen_norm (h:1≤t) : ‖x‖ ≤ Sen o t x:=tore_aux
  where
  tore_aux : ‖x‖ ≤ Sen o t x:=by
    change ‖x.val‖ ≤ visc _ _ _
    rw [Grass.norm_def, pricesD _ (zero_le_one.trans h)]; refine Finset.sum_le_sum (fun i _=>le_mul_of_one_le_left (norm_nonneg _) ?_)
    exact one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr (one_le_pow₀ (by omega))) (one_le_pow₀ h)
lemma sen_tsum {I:Type*} (f:I→EvenA p N) (g:I→ℝ) (hg:Summable g)(hf:Summable f)(he:∀ i,Sen o t (f i) ≤ g i): Sen o t (∑' i,f i) ≤ ∑' i,g i:=by
    let F:= needle o N t
    change ‖F _‖≤ _; rw [F.map_tsum hf]; have hx: Summable (fun i=> ‖F (f i)‖) := hg.of_nonneg_of_le (fun i=>norm_nonneg _) he
    exact (norm_tsum_le_tsum_norm hx).trans (hx.tsum_le_tsum he hg)
open Massive.Log (log rev)
lemma rev_pay (h:1≤t)(hx:Sen o t x≤1/8) : Sen o t (rev x) ≤2:=by
    let z:ℝ:=1/2; have hm:=hx.trans (by norm_num : 1/8 ≤ z); have hN := (sen_norm (o:=o) t x h).trans_lt (hm.trans_lt one_half_lt_one)
    rw [Massive.Log.rev_eq]; refine (sen_tsum t _ (fun n=> z^n) summable_geometric_two ((Massive.Log.alive hN).of_norm) ?_).trans_eq tsum_geometric_two
    intro i; exact (sen_pow t _ (zero_le_one.trans h) i).trans (pow_le_pow_left₀ (sen_nonneg ..) ((sen_neg t x).le.trans hm) i)
lemma log_pay (h:1≤t)(hx:Sen o t x≤w)(he:w≤1/8) : Sen o t (log x) ≤2*w:=by
    let z:ℝ:=1/2; have ht0:0≤w:=(sen_nonneg ..).trans hx; have hm:=he.trans (by norm_num : 1/8 ≤ z); have hN := (sen_norm (o:=o) t x h).trans_lt (hx.trans_lt (hm.trans_lt one_half_lt_one))
    let g(n:ℕ):ℝ:=match n with|0=>0|n+1=>z^n*w
    have hg : HasSum g (2*w):=by
       apply (hasSum_nat_add_iff' 1).mp; rw [Finset.sum_range_one,show g 0=0 from rfl,sub_zero]; exact hasSum_geometric_two.mul_right w
    rw [Massive.Log.log_eq]; refine (sen_tsum  t _ g hg.summable ((Massive.Log.afford hN).of_norm) ?_).trans_eq hg.tsum_eq
    intro n; rw [sen_real]; cases n
    · simp [g,Massive.Log.c]
    next n=> refine (mul_le_of_le_one_left (sen_nonneg ..) (Massive.Log.priced _)).trans ((sen_pow t x (zero_le_one.trans h) _).trans ?_); rw [pow_succ]; exact mul_le_mul (pow_le_pow_left₀ (sen_nonneg ..) (hx.trans hm) _) hx (sen_nonneg ..) (by unfold z; positivity)
open Massive.Log
section
variable {k l:ℕ} {f: Config G n→EvenA p N}{V:Config G n}
-- derivative formulas in neighborhoods of strictly small values
private lemma near_small (ht:Chart k f V)(hm:‖f V‖ <1/4): ∀ᶠ v in 𝓝 0, ‖(f ∘ increment V) v‖<1/4 := ht.continuousAt.norm.eventually (gt_mem_nhds (by simpa [Work.G07.at_zero_increment] using hm))
private lemma logchart (ht:Chart k f V)(hm:‖f V‖ <1/4): Chart k (log ∘ f) V := ((basicL (hm.trans (by norm_num))).contDiffAt.of_le le_top).comp_of_eq 0 ht (by intro i h; trivial) (by simp)
private lemma revchart (ht:Chart k f V)(hm:‖f V‖ <1/4): Chart k (rev ∘ f) V := ((basicR (hm.trans (by norm_num))).contDiffAt.of_le le_top).comp_of_eq 0 ht (by intro i h; trivial) (by simp)
set_option quotPrecheck false
local notation "L"=>log ∘ f
local notation "Z"=>rev ∘ f
local notation "V₁"=> (1: Config G n→EvenA p N)
lemma right_one (A:Directions G n)(g:Config G n→EvenA p N)(he:Chart 1 g V) : leftDerivs (V₁+g) [A] V= leftDerivs g [A] V :=by
    rw [left_add [A] (show Chart 1 V₁ V from contDiffAt_const) he le_rfl,show leftDerivs V₁ [A] V=0 from YM.Work.G07.left_const 1 [A] V]; exact zero_add _
lemma first_inv (ht: Chart 1 f V) (hm: ‖f V‖ < 1/4) (A:Directions G n) : leftDerivs (Z) [A] V= - ((Z) V)^2*leftDerivs f [A] V :=by
    let g := V₁+f; have hg : Chart 1 g V:= (show Chart 1 V₁ V from contDiffAt_const).add ht
    have hF : (g*(Z)) ∘ increment V =ᶠ[𝓝 0] fun _=> (1: EvenA p N):=by
       filter_upwards [near_small ht hm] with v hv; exact inverse (hv.trans (by norm_num : (1/4:ℝ)<1))
    have hZ:= left_congr [A] V (f:=g*(Z)) (g:=V₁) hF
    rw [left_first_mul A hg (revchart ht hm),show leftDerivs V₁ [A] V=0 from Work.G07.left_const 1 [A] V, show g= V₁+f from rfl,right_one A f ht] at hZ
    let F:= g V; let B:=leftDerivs f [A] V; let Y:= leftDerivs (Z) [A] V
    have hT : F*(Z) V=1:= inverse (hm.trans (by norm_num))
    change B*(Z) V+F*Y= _ at hZ
    calc
      Y=Y+(Z) V * 0:=by ring
      _ = Y-(Z) V*(B*(Z) V+F*Y):=by rw [hZ]; ring
      _ = (1-F*(Z) V)*Y+-((Z) V)^2*B := by ring
      _=_:=by rw [hT]; simp [B]
lemma first_log (hf:Chart 1 f V)(hm:‖f V‖ <1/4)(A:Directions G n): leftDerivs (L) [A] V=(Z) V* leftDerivs f [A] V:=by
    let v(t:ℝ):=increment V (t • A); have hv : v 0= V:=by unfold v; rw [zero_smul,Work.G07.at_zero_increment]
    have he(t)(ht:‖f (v t)‖<1/4) : NormedSpace.exp ((L) (v t))= 1+f (v t):= cancel ht.le
    let U:= leftDerivs (L) [A] V; let C:=leftDerivs f [A] V
    have hh':ContinuousAt (f ∘ v) 0 := (show ContDiffAt ℝ (↑(1:ℕ)) (f ∘ v) 0 from chart_comp (f:=f) (by rw [hv]; exact hf) fun i=> increment_curve ..).continuousAt
    have hh: ∀ᶠ t in 𝓝 (0:ℝ), ‖f (v t)‖<1/4 := hh'.norm.eventually (gt_mem_nhds (show ‖(f ∘ v) 0‖<1/4 by simp only [comp_apply,hv]; exact hm))
    let F := (1+f V); have ha:NormedSpace.exp ((L) (v 0)) = F:= he 0 (hv.symm ▸ hm) |>.trans (hv ▸ rfl)
    have ht: HasDerivAt (fun t=>1+f (v t)) (F*U) 0:=by
       refine ((show HasDerivAt (fun t:ℝ=>NormedSpace.exp ((L) (v t))) (NormedSpace.exp ((L) (v 0))*U) 0 from by
         let value:= ((L) ∘ v) 0
         have hp:= hasFDerivAt_exp (𝕂:=ℝ) (x:=value)
         have hy:= hp.comp_hasDerivAt 0 (show HasDerivAt ((L) ∘ v) U 0 from left_has (l:=[]) A (by simp) (logchart hf hm)); exact hy ).congr_deriv ?_).congr_of_eventuallyEq ?_
       · rw [ha]
       exact hh.mono fun i hi=> (he i hi).symm
    have hB:F*U=C:= ht.unique ((left_has (l:=[]) A (by simp) hf).const_add (1: EvenA p N))
    calc
      U=(Z) V*(F*U):=by rw [←mul_assoc,mul_comm ((Z) V),show F*(Z) V=1 from inverse (hm.trans (by norm_num)),one_mul]
      _=_:=by rw [hB]

variable {t w} {d:Directions G n→Prop}
-- constants explicit, intentionally allowed to be large at the fixed order
abbrev Paid (o:Site p) (t:ℝ) (f: Config G n→EvenA p N) (V: Config G n)(D: Directions G n→Prop)(k:ℕ)(a:ℝ) := Chart k f V ∧ ∀ l, List.length l ≤ k→ (∀ v∈l,D v)→ Sen o t (leftDerivs f l V)≤a
lemma Paid.non (h: Paid o t f V d k w) : 0 ≤ w:= (sen_nonneg ..).trans (h.2 [] (Nat.zero_le _) (by simp))
lemma Paid.low {a' :ℝ}(h: Paid o t f V d k w)(he:l≤ k)(hm:w≤a') : Paid o t f V d l a':= ⟨h.1.of_le (Nat.cast_le.mpr he),fun i hi hd=>(h.2 i (hi.trans he) hd).trans hm⟩
lemma Paid.out {a' :ℝ} {g: Config G n→EvenA p N}(h: Paid o t f V d k w)(ht:0 ≤ t)(h': Paid o t g V d k a'): Paid o t (f*g) V d k (2^k*(w*a')):=by
    refine ⟨h.1.mul h'.1, fun j hj hV=> (left_mul_sen o t ht h.1 h'.1 h.2 h'.2 j hj hV).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (mul_nonneg h.non h'.non)
lemma Paid.pre (h: Paid o t f V d k w)(he:l < k)(A:Directions G n)(hD:d A): Paid o t (leftDerivs f [A]) V d l w:=by
     refine ⟨leftDerivs_chart _ _ (h.1.of_le (Nat.cast_le.mpr (by simp only [List.length_cons,List.length_nil,Nat.zero_add]; omega))),?_⟩
     intro j hj hv; rw [← Work.G07.left_append]; exact h.2 _ (by simp; omega) (List.forall_mem_append.mpr ⟨hv,by simpa using hD⟩)
lemma Paid.neg (h:Paid o t f V d k w): Paid o t (-f) V d k w:=by
    let F: EvenA p N→L[ℝ]EvenA p N:= - ContinuousLinearMap.id ℝ (EvenA p N); refine ⟨h.1.neg,fun i hi hp=>?_⟩
    rw [show -f=F ∘ f from rfl,left_linear F _ h.1 hi,show ∀ x:EvenA p N,F x= -x from fun _=>rfl,sen_neg]; exact h.2 i hi hp
noncomputable def cInv : ℕ→ℝ
 | 0=>2
 | n+1=>cInv n + (2^n)^2*cInv n^2
lemma cInv_head (k:ℕ):2 ≤ cInv k:=by induction k with|zero=>exact le_rfl|succ n ih=> exact ih.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
lemma cInv_mono (k:ℕ):cInv k≤cInv (k+1):=le_add_of_nonneg_right (by positivity :0 ≤ (2^k:ℝ)^2*cInv k^2)
lemma Paid.inv {d:Directions G n→Prop}(h: Paid o t f V d k w)(hf:1≤t)(ht:w≤1/8): Paid o t (Z) V d k (cInv k):=by
    have h0:Sen o t (f V)≤1/8:=(h.2 [] (Nat.zero_le _) (by simp)).trans ht; have hm : ‖f V‖<1/4:= (sen_norm (o:=o) t _ hf).trans_lt (h0.trans_lt (by norm_num))
    induction k with
    | zero=> refine ⟨revchart h.1 hm,fun l hl _=>?_⟩; rw [List.eq_nil_of_length_eq_zero (le_antisymm hl (Nat.zero_le _))]; exact rev_pay t _ hf h0
    | succ k ih=>
         have hr:= ih (h.low (Nat.le_add_right ..) le_rfl); have he :Chart 1 f V:=h.1.of_le (Nat.cast_le.mpr (by omega)); refine ⟨revchart h.1 hm,?_⟩
         intro l hl hB; cases l using List.reverseRecOn with
         | nil=> exact (hr.2 [] (Nat.zero_le _) (by simp)).trans (cInv_mono _)
         | append_singleton l A =>
             have ht': l.length≤ k:=by simpa using hl
             have hd: leftDerivs (Z) [A] ∘ increment V =ᶠ[𝓝 0] ((- ((Z)*(Z))) * leftDerivs f [A]) ∘ increment V:=by
               have hX: ∀ᶠ x in 𝓝 0, Chart 1 f (increment V x) := chart_eventually (by rw [Work.G07.at_zero_increment]; exact he) (fun i=>by simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt)
               filter_upwards [hX,near_small h.1 hm] with x hx hz; exact (first_inv hx hz _).trans (by rw [pow_two]; rfl)
             rw [Work.G07.left_append, left_congr _ _ hd]; have hpA:= (List.forall_mem_append.mp hB)
             let F0:= cInv k; have hu:0≤t:=zero_le_one.trans hf
             apply (( ((hr.out hu hr).neg).out hu (h.pre (by omega) A (hpA.2 _ (by simp))) ).2 _ ht' hpA.1).trans
             have ht:w ≤1 := ht.trans (by norm_num); calc
                 _ ≤ (2^k:ℝ) * (2^k * (F0*F0)*1):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (by unfold F0; have hx:=cInv_head k; positivity)) (by positivity)
                 _=((2^k:ℝ)^2*F0^2):=by ring
                 _ ≤ _:=le_add_of_nonneg_left (by linarith [cInv_head k])
lemma Paid.logP (h:Paid o t f V d k w) (hf:1≤t) (ht:w≤1/8): Paid o t (L) V d k (2^k*cInv k*w):=by
    let c:=2^k*cInv k; have hw:0 ≤ w:=h.non
    have hh:=h.inv hf ht; have h0:Sen o t (f V)≤w:=h.2 [] (Nat.zero_le _) (by simp); have hm : ‖f V‖ <1/4:= (sen_norm (o:=o) t _ hf).trans_lt (h0.trans_lt (ht.trans_lt (by norm_num)))
    refine ⟨logchart h.1 hm,?_⟩
    intro l hl hv; cases l using List.reverseRecOn with
     | nil=> exact (log_pay w t _ hf h0 ht).trans (mul_le_mul_of_nonneg_right (by nlinarith only [one_le_pow₀ (n:=k) (by norm_num : (1:ℝ)≤2), cInv_head k]) hw)
     | append_singleton l A=>
        have he: Chart 1 f V:=h.1.of_le (Nat.cast_le.mpr (by simp only [List.length_append,List.length_cons,List.length_nil] at hl; omega)); have hL:l.length<k:=by simpa using hl
        have hd: leftDerivs (L) [A] ∘ increment V =ᶠ[𝓝 0] ((Z)*leftDerivs f [A])∘ increment V:=by
               have hX: ∀ᶠ x in 𝓝 0, Chart 1 f (increment V x) := chart_eventually (by rw [Work.G07.at_zero_increment]; exact he) (fun i=>by simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt)
               filter_upwards [hX,near_small h.1 hm] with x hx hz; exact first_log hx hz _
        rw [Work.G07.left_append,left_congr _ _ hd]; have hP:= (List.forall_mem_append.mp hv)
        apply ((((hh.low hL.le le_rfl).out (zero_le_one.trans hf) (h.pre hL A (hP.2 _ (by simp)))).2 l le_rfl hP.1)).trans
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hL.le) (mul_nonneg (by linarith [cInv_head k]) hw)
end

section f
variable {X : Support p} {t w u: ℝ} {P:BudgetPoint}{F G : Grid p→ EvenA p N} (hF: Woven o X P t F w)
include hF
lemma mullP (hG: Woven o X P t G u)(ht:0≤t): Woven o X P t (F*G) (2^P.order*(w*u)) := by
    refine ⟨fun i j h=>congr_arg₂ (·*·) (hF.room i j h) (hG.room i j h),?_ ,fun i hi=> (hF.use _ hi).mul (hG.use _ hi), fun V hv=>?_ ,hF.Borel.mul hG.Borel,mul_nonneg (by positivity) (mul_nonneg hF.travel hG.travel)⟩
    · intro i; unfold Gated; rw [Pi.mul_apply,map_mul]; exact Subalgebra.mul_mem _ (hF.gated _) (hG.gated _)
    exact ((show Paid o t F V (P.dirBound o) P.order w from ⟨hF.use _ hv,hF.pole _ hv⟩).out ht ⟨hG.use _ hv,hG.pole _ hv⟩).2
open MeasureTheory NormedSpace
lemma logP (ht:1≤t)(he:w≤1/8): Woven o X P t (log ∘ F) (2^P.order*cInv P.order*w):=by
    have hp (i : Grid p)(h: Healthy P.threshold X i):=Paid.logP (show Paid o t F i (P.dirBound o) P.order w from ⟨hF.use i h,hF.pole i h⟩) ht he
    refine ⟨fun i j h=> congr_arg log (hF.room i j h), fun i=>?_,fun i h=> (hp i h).1,fun i h=> (hp i h).2,?_,mul_nonneg (mul_nonneg (by positivity) (by linarith [cInv_head P.order])) hF.travel⟩
    · rw [Function.comp_apply, Massive.Log.log_eq]; apply spearm; intro j; unfold Gated; apply club; unfold Gated; rw [map_pow]; exact Subalgebra.pow_mem _ (hF.gated _) _
    have h : ∀ x :Grid p, (log ∘ F) x= ∑' n:ℕ, Massive.Log.c n • F x^n:=fun _=> log_eq _; simp_rw [show (log ∘ F)=_ from funext h]; apply Measurable.tsum; intro i; exact measurable_const.smul (hF.Borel.pow_const _)
-- complex scalar version.
lemma scaleP (c:ℂ):Woven o X P t (c • F) (‖c‖*w):=by
    have he(U:Grid p)(hx:Healthy P.threshold X U): Chart P.order (c • F) U := contDiffAt_const.smul (hF.use U hx)
    have ha :∀ U:Grid p,Gated X ((c • F) U) := by intro i; unfold Gated; rw [Pi.smul_apply,map_smul]; exact Subalgebra.smul_mem _ (hF.gated _) _
    refine ⟨fun i j h=> congr_arg (c • ·) (hF.room i j h),ha,he,?_, measurable_const.smul hF.Borel,mul_nonneg (norm_nonneg _) hF.travel⟩
    intro i hv l hl hx; let Q: EvenA p N→L[ℝ]EvenA p N:= (c • ContinuousLinearMap.id ℂ (EvenA p N)).restrictScalars ℝ
    rw [show c • F=Q ∘ F from rfl,left_linear Q _ (hF.use i hv) hl]; let x:=leftDerivs F l i
    change ‖needle o N t (c • x)‖≤_; rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (hF.pole _ hv l hl hx) (norm_nonneg _)
end f
end YM.QCD.Lime
#print axioms YM.QCD.Lime.logP
#print axioms YM.QCD.Lime.mullP
#print axioms YM.QCD.Lime.scaleP
