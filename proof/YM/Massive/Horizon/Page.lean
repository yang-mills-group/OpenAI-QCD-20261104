import YM.QCD.Dust.Rose
/-! Step spin fee grade3. No flavor-blindness here, through-weight-3 non-plaquette regular only, or mass-bearing for grade2 quote. We use the constraints on the pair itself directly. Adapts Brick.Perk, Dust.Pages & Dust.Rose. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
variable {c f : Side} {F:Kit.Rail f c}{N m:ℕ}{o:Site f}{w:Keys c N→ℕ}{p r q t v C:ℝ}{D:Type*}[Fintype D]{b:Bool}
variable {L':Side}(hA:∀ i:Accent N,Lien w (fern L') p (C*t*cape L' 0) (staff o F i)) (hp:0<p)(ht:0<t)(he:0≤C) (h :640*C*cape L' 0≤1)
include hA hp ht h he
lemma split_rebate (X: EvenA f N)(hC: coef ∅ X.val=0)(hv:panel 2 X.val=form (grasp X.val))(hQ:lights o b (grasp X.val)): visc w p (apple F N X.val) ≤ (coreP C+ ott C)* nickel L' b* Sen o t X:=by
   let v:= C*t*cape L' 0; have hx :0≤ v:= by unfold v; positivity [cape_pos L' 0]
   let q:= nickel L' b; let r:= fern L'; have hr:0<r:=fern_pos L'
   let Z:= Stew.stage 2 X; let P':=(X-Z).val; have hz: X.val=Z.val+P':=by change _=Z.val+(X.val-Z.val); abel
   let B:= Sen o t X; have hB:0≤B:=norm_nonneg _; let R:=grasp X.val; have hd: Z.val=form R:=hv
   have hu := sumBl o X.val ht.le
   have ht₁ : visc w p (apple F N Z.val) ≤ coreP C*q * B:=by
      let T:= ∑ i,∑ j, ‖R i j‖* ↑(pieD (Stew.lens o) (tag i j))
      rw [hd]; refine (river o R hQ hA hp hr.le (fern_one L') hx).trans (le_trans ?_ (mul_le_mul_of_nonneg_left hu (show 0 ≤ coreP C*q by unfold coreP q nickel; positivity [fern_pos L'])))
      change _ ≤ coreP C*q*(T* t^2); unfold coreP q tips nickel; cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> simp_rw [mul_pow,capeQ]; all_goals unfold T R; exact le_of_eq (by ring) -- watch simp
   have hp₀: visc w p (apple F N P') ≤ ott C*q*B:=by
      apply (taxi hA hp ht he h P' (vacant2 _ hC)).trans; have hx: Stew.plank o t P' ≤ 2*B := (vertex X.val Z.val).trans (by rw [two_mul]; exact add_le_add le_rfl (Stew.absolute o 2 X ht.le))
      refine (mul_le_mul_of_nonneg_left hx (show 0 ≤ (640 * C * cape L' 0)^4 by positivity [cape_pos L' 0])).trans ?_
      have hg : cape L' 0 ^4 ≤ q:= by rw [show 4=2*2 from rfl,pow_mul,capeQ,← pow_mul]; apply pow_le_pow_of_le_one (fern_pos L').le (fern_one L') (by split <;> norm_num)
      rw [mul_pow (640*C)]; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (pow_nonneg (by linarith) _)) (by linarith : 0≤2*B)).trans_eq (by unfold ott; ring)
   calc
     _ = visc w p (apple F N (Z.val+P')):=by apply congr_arg; exact congr_arg _ hz
     _ ≤ (coreP C+ ott C)*q* B:= by rw [map_add]; exact (vested ..).trans ((add_le_add ht₁ hp₀).trans_eq (by ring))
end YM.QCD.Brick
namespace YM.QCD.Dust
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Brick
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent Reggae
open PhysicalNext.JointLoad MultiNext.SignedSource
variable {c f L:Side} {j k N n:ℕ} {C h1 h2 u v w A t:ℝ} {X:Support f}{o:Site f}{R:BudgetPoint}{a:Site c}
variable {M:Grid f→EvenA f N}

variable {S:Kit.Rail f c}(K: Hera.Rights su k) (hp: Woven o X R t M C)

def Unfeatured (o:Site f)(x:EvenA f N):Prop:=panel 2 x.val=form (grasp x.val) ∧ lights o false (grasp x.val)
structure Loan (massless:Bool)(M: Grid f→EvenA f N)(o:Site f):Prop where
    no : ∀ U,mud (M U)=0
    gauge:shadeG M
    flat : massless → Unfeatured o (M 1)
abbrev furl (b:Bool):ℕ:= 3+(if b then 1 else 0)
variable (hQ:∀ i:Accent N,Lien (Stew.lens a) (fern L) u (v*t*cape L 0) (staff o S i))(h:0<u) (ht:0<t) (hV:0 ≤ v) (hv:640*v*cape L 0≤1) {isR:Bool}(hM:Loan isR M o)
variable (g: Crate c N →L[ℝ]ℝ)(he:∀ x,‖g x‖ ≤ Stew.plank a u x)
lemma priceable (v:ℝ): 0 ≤ coreP v+ott v∧ (640*v)^2≤Jive v∧ coreP v+ott v ≤ Jive v:=by
    unfold Jive coreP ott; refine ⟨by positivity,?_,?_⟩ <;> nlinarith [sq_nonneg v,pow_nonneg (by have hh:=sq_nonneg v; exact hh) 2]
include hp hQ h ht hV hv hM he
lemma priceLoan :
    let F:= (g.comp (bill S N) ∘ M); let Q:=Jive v*C
    0 ≤ Q∧ Ease.Charm R X F ∧ R.supBounds o X F (Q*fern L^3) ∧ ‖F 1‖ ≤ Q*fern L^(furl isR) := by
    intro F Q
    let y:= (g.comp (bill S N)); let a':= fern L; have ht':0<a':=fern_pos L
    have hp0:=hp.travel
    obtain ⟨h₀,hp₁,hp₂⟩:= priceable v
    have hL:0≤ Jive v:= h₀.trans hp₂
    have ha: Ease.Charm R X M:= ⟨hp.room,hp.use⟩
    have hF:=ha.scales y
    refine ⟨mul_nonneg hL hp0,hF,⟨by have hQ:0≤Q:=mul_nonneg hL hp0; positivity [fern_pos L],?_⟩,?_⟩
    · intro U hU l hh hx; rw [left_linear _ _ (hp.use U hU) hh]; apply (he _).trans; refine (broad hQ h ht hV hv _ (leftovers hp hM.no U hU l hh)).trans ?_
      exact (mul_le_mul (mul_le_mul_of_nonneg_right hp₁ (pow_nonneg ht'.le _)) (hp.pole _ hU l hh hx) (norm_nonneg _) (by positivity [fern_pos L])).trans_eq (by unfold Q; ring)
    cases isR
    · apply (he (bill S N (M 1))).trans
      apply (broad hQ h ht hV hv _ (hM.no 1)).trans; exact (mul_le_mul (mul_le_mul_of_nonneg_right hp₁ (pow_nonneg ht'.le _)) (hp.sizeU _ (AnalyticBridge.VerifiedReset.flat_ok ..)) (norm_nonneg _) (mul_nonneg hL (pow_nonneg ht'.le _))).trans_eq (by unfold Q a';change _= _*fern L^3;ring)
    · apply (he (bill S N (M 1))).trans; have hx:= split_rebate hQ h ht hV hv _ (hM.no 1) (hM.flat rfl).1 (hM.flat rfl).2
      apply hx.trans; have hu: nickel L false =a'^4:=rfl; rw [hu]; exact (mul_le_mul (mul_le_mul_of_nonneg_right hp₂ (pow_nonneg ht'.le _)) (hp.sizeU _ (AnalyticBridge.VerifiedReset.flat_ok ..)) (norm_nonneg _) (mul_nonneg hL (pow_nonneg ht'.le _))).trans_eq (by unfold Q a';change _= _*fern L^4;ring)
end YM.QCD.Dust
namespace YM.PhysicalNext.JointLoad.Hera
open MultiNext.SignedSource.Ease
open Function Filter Lattice Wilson RG Next.Foundations
    AnalyticBridge.VerifiedReset MultiNext.SignedSource MultiNext.SignedSource.Mom MultiNext.SignedSource.Banjo
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {B : BudgetPoint} {X : Support n} {o : Site n} {m k : ℕ} {C r τ : ℝ}
    {f : Config G n → ℝ}


variable (h : Charm B X f)(hr: 0≤r)(ht:r≤1)(hc:1≤C)(Q:Rights G k)(hk:k ≤ B.order)(hw:0≤ τ)(hb: B.supBounds o X f (τ*r^3))
variable (kz:ℕ)(hz:kz ≤ 1)(h₀:‖f 1‖ ≤ τ*r^(3+kz))
include h hr ht hc hk hw hb h₀ hz
private lemma mica3 (m:ℕ)(hm : m ≤ k) (v : Fin m→ Directions G n)(hv : ∀ i, Promise 2 C r B o X (v i)):
    ‖iteratedFDeriv ℝ m (f ∘ increment 1) 0 v‖≤ ((3*((3*C)^k*r^(3+kz)))*Q.fee)*τ :=by
    have hh : 1 ≤3*C:=by linarith
    have he : 1 ≤ (3*C)^k := one_le_pow₀ hh; have hx:= Q.large
    by_cases hs:m=0
    · subst m; rw [iteratedFDeriv_zero_apply, Function.comp_apply,YM.Work.G07.at_zero_increment]; apply h₀.trans; rw [mul_comm τ]; let b:=(3*C)^k; have hA:1≤3*b*Q.fee:=by unfold b; nlinarith only [he,hx]
      refine mul_le_mul_of_nonneg_right ?_ hw; exact (le_mul_of_one_le_left (pow_nonneg hr _) hA).trans_eq (by unfold b; ring)
    have h:= Q.born 1 v (fun _=>3*C*r) hm (hm.trans hk) h hb (flat_ok ..) (fun i=>by convert (hv i).shot hr ht (zero_le_one.trans hc) using 1; norm_num)
    apply h.trans; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rw [mul_pow]; let s:=3*C; have hx':(3*C)^m*r^m ≤ (3*C)^k*r^kz:=mul_le_mul (pow_le_pow_right₀ hh hm) (pow_le_pow_of_le_one hr ht (by omega)) (pow_nonneg hr _) (by positivity); refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx' (show 0 ≤Q.fee by positivity)) (show 0 ≤ τ*r^3 by positivity)).trans ?_
    calc
      _=(3*C)^k*r^(3+kz)*Q.fee*τ:=by rw [pow_add]; ring
      _ ≤ _:=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) (by norm_num)) (zero_le_one.trans hx)) hw)
lemma crystal3 (u : Directions G n) (hu : Promise 2 C r B o X u) (he : ∀ e, needed X e → ‖u e‖ ≤ 1 ∧ Lyre.width B o e ≤ 1)
    (hs : ∀ t ∈ Set.Icc (0:ℝ) 1, Healthy B.threshold X (increment 1 (t • u))) (hK : 2 ≤ k) (hm : m ≤ k) (v : Fin m → Directions G n)
    (hv : ∀ j, Promise 2 C r B o X (v j)) : ‖iteratedFDeriv ℝ m (f ∘ increment 1) u v‖ ≤ (k+1:ℝ)*(3*((3*C)^k*r^(3+kz))) * Q.fee * τ := by
  let F := f ∘ increment (1:Config G n); let z := (3*((3*C)^k*r^(3+kz)))*Q.fee*τ
  have h0 := Q.large; have hτ := hw
  have H (j) (hj : j ≤ k) (v : Fin j → Directions G n) (hv : ∀ i, Promise 2 C r B o X (v i)) (s : ℝ) (ht' : s ∈ Set.Icc (0:ℝ) 1) :
      ‖iteratedFDeriv ℝ j F (s • u) v‖ ≤ ((k+1-j:ℕ):ℝ)*z := by
    have Hs t i (ht₀ : t ∈ Set.Icc (0:ℝ) 1) (hi : i ≤ k) : ContDiffAt ℝ (i:ℕ∞ω) F (t • u) := (Hera.along h (hs t ht₀)).of_le (Nat.cast_le.mpr (hi.trans hk))
    induction hj using Nat.decreasingInduction generalizing s with
    | self =>
      rw [show k+1-k=1 by omega,Nat.cast_one,one_mul]
      apply (Q.moves 1 _ v (fun _ => 3*C*r) le_rfl hk h hb (hs _ ht') ?_ ?_).trans
      · simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow]
        have hh:= mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr ht (show kz ≤ k by omega)) (show 0≤ (3:ℝ)^k*C^k from by positivity)
        change _*Q.fee*(τ*r^3) ≤ z
        refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (show 0≤τ*r^3 by positivity)).trans ?_
        unfold z; simp only [mul_pow]; calc
           _ = ((3:ℝ)^k*C^k*r^(3+kz))*Q.fee*τ:=by rw [pow_add]; ring
           _ ≤ _:=by exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) (by norm_num)) (zero_le_one.trans h0)) hτ
      · intro i hi; rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg ht'.1]; exact ⟨mul_le_one₀ ht'.2 (norm_nonneg _) (he i hi).1,(he i hi).2⟩
      intro i; convert (hv i).shot hr ht (zero_le_one.trans hc) using 1; norm_num
    | of_succ j hj ih =>
      have ha : ∀ i : Fin (j+1), Promise 2 C r B o X ((Fin.cons u v : Fin (j+1) → Directions G n) i) := Fin.cases (by simpa using hu) (fun i => by simpa using hv i)
      have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t : ℝ => iteratedFDeriv ℝ j F (t • u) v) (fun x hx => (Heir.along_deriv u v x (Hs x (j+1) hx hj)).hasDerivWithinAt)
        (fun x hx => ih (Fin.cons u v) ha x hx) (convex_Icc ..) (show (0:ℝ)∈Set.Icc (0:ℝ) 1 by simp) ht'
      rw [zero_smul,sub_zero, Real.norm_of_nonneg ht'.1] at H
      have hp := H.trans (mul_le_of_le_one_right (by unfold z; positivity) ht'.2)
      have he : ‖iteratedFDeriv ℝ j F 0 v‖ ≤ z := mica3 h hr ht hc Q hk hw hb kz hz h₀ j (Nat.le_of_lt hj) v hv
      refine (norm_le_of_pair hp he).trans_eq ?_
      rw [show k+1-j=k+1-(j+1)+1 by omega, Nat.cast_add_one, add_mul,one_mul]
  have hx := H m hm v hv 1 (by simp); rw [one_smul] at hx
  refine hx.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) (by unfold z; positivity)).trans_eq ?_); unfold z; push_cast; ring
where norm_le_of_pair {x y a b : ℝ} (h : ‖x-y‖ ≤ a) (he : ‖y‖ ≤ b) : ‖x‖ ≤ a+b :=
  (by simpa using (norm_add_le (x-y) y).trans (add_le_add h he))
end YM.PhysicalNext.JointLoad.Hera

#print axioms YM.QCD.Dust.priceLoan
#print axioms YM.PhysicalNext.JointLoad.Hera.crystal3
