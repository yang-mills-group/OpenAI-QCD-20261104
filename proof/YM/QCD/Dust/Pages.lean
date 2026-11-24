import YM.QCD.Brick.Perk
import YM.QCD.Reggae.Ruma
/-! # sharp linear regular norms of the nonconstant Grass sector. test all ξ hats. A Estr right orientation selected through `Mark`. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Dust
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Brick
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent Reggae
open PhysicalNext.JointLoad MultiNext.SignedSource
variable {c f L:Side} {j k N n:ℕ} {C h1 h2 u v w A t:ℝ} {X:Support f}{o:Site f}{R:BudgetPoint}{a:Site c}
variable {M:Grid f→EvenA f N}
abbrev wash (o:Site f)(N:ℕ)(p:ℝ): EvenA f N →L[ℝ] (Crate f N):= ContinuousLinearMap.restrictScalars ℝ (needle o N p)
lemma commune {X:Crate f N}:∃ g: Crate f N→L[ℝ]ℝ, ‖g‖ ≤1∧ ‖X‖=‖g X‖:=by
    rcases eq_or_ne X 0 with rfl|h; · exact ⟨0,by simp,by simp⟩
    obtain ⟨g,hg,h⟩:= exists_dual_vector ℝ X (norm_ne_zero_iff.mpr h); change g X=(‖X‖:ℝ) at h; exact ⟨g,hg.le,by rw [h,Real.norm_of_nonneg (norm_nonneg _)]⟩
variable {S:Kit.Rail f c}(K: Hera.Rights su k) (hp: Woven o X R t M C)
include hp
lemma leftovers (h:∀ U,mud (M U)=0)(x:Grid f)(he:Healthy R.threshold X x)(l:List (Directions su f))(ht:l.length ≤ R.order) : mud (leftDerivs M l x)=0:=by
   change ((clay f N).restrictScalars ℝ) _ = _; rw [←left_linear _ _ (hp.use x he) ht]
   rw [show (⇑((clay f N).restrictScalars ℝ) ∘ M) =(fun _=> (0:ℂ)) from funext h]
   by_cases hv:l=[]; · subst l; rfl
   cases l with
   | nil=> contradiction
   | cons i l=> exact YM.Work.G07.left_const (0:ℂ) (i::l) x -- signature
lemma breath {L: EvenA f N→L[ℝ]ℝ}{X':ℝ}(hh:∀ x, ‖L x‖≤X' * Sen o t x)(hr: 0≤X'): R.supBounds o X (L ∘ M) (X'*C):= by
   refine ⟨mul_nonneg hr hp.travel,?_⟩; intro V hv l hl hk; rw [left_linear _ _ (hp.use _ hv) hl]; exact (hh _).trans (mul_le_mul_of_nonneg_left (hp.pole _ hv _ hl hk) hr)
-- incoming metric tensors
lemma aural (U:Grid f)(he:Healthy R.threshold X U) (l:Fin n→Directions su f)(q:Fin n→ℝ)(hh:n≤k)(hR:n≤R.order)(hs:∀ i,Lyre.Sized (q i) (l i) R o): Sen o t (iteratedFDeriv ℝ n (M ∘ increment U) 0 l) ≤(∏ i,q i)* K.fee * C:=by
    let x:= iteratedFDeriv ℝ n (M ∘ increment U) 0 l; obtain ⟨g,hg,h⟩:= commune (X:=wash o N t x)
    let V:= g.comp (wash o N t)
    have ht (x): ‖V x‖≤1*Sen o t x:= (g.le_opNorm _).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
    have hp' : Ease.Charm R X M:=⟨hp.room,hp.use⟩
    have hh': R.supBounds o X (V ∘ M) C:=by rw [← one_mul C]; exact breath hp ht zero_le_one
    have H: V x= iteratedFDeriv ℝ n ((V ∘ M) ∘ increment U) 0 l:=by
       unfold x; rw [show iteratedFDeriv ℝ n ((V ∘ M) ∘ increment U) 0 = _ from V.iteratedFDeriv_comp_left (hp.use U he) (Nat.cast_le.mpr hR)]; rfl
    apply le_trans (b:= ‖V x‖) h.le; rw [H]; exact K.born U l q hh hR (hp'.scales V) hh' he hs
-- working with A: all purchase applied to a real functional. spends can be spurred later (test rotates outputs, metric proof separate).
structure Sign (M: Grid f→EvenA f N)(b:Flavor N)(o:Site f):Prop where
    no : ∀ U,mud (M U)=0
    gauge:shadeG M
    flavor : ∀ U,Fit (M U)
    heads :∀ i, shape o (feeF b (M 1)) i=0
variable (hQ:∀ i:Accent N,Lien (Stew.lens a) (fern L) u (v*t*cape L 0) (staff o S i))(h:0<u) (ht:0<t) (hV:0 ≤ v) (hv:640*v*cape L 0≤1) {b:Flavor N}(hM:Sign M b o)
abbrev bill (S:Kit.Rail f c)(N:ℕ): EvenA f N→L[ℝ] Crate c N:= ContinuousLinearMap.restrictScalars ℝ (((apple S N).comp (Cove.light _)).toLinearMap.toContinuousLinearMap)
variable (g: Crate c N →L[ℝ]ℝ)(he:∀ x,‖g x‖ ≤ Stew.plank a u x)
omit hp
def Jive (v:ℝ):ℝ:=1+(640*v)^2+coreP v+ott v
private lemma virtue (v:ℝ): 0 ≤ coreP v+ott v∧ (640*v)^2≤Jive v∧ coreP v+ott v ≤ Jive v:=by
    unfold Jive coreP ott; refine ⟨by positivity,?_,?_⟩ <;> nlinarith [sq_nonneg v,pow_nonneg (by have hh:=sq_nonneg v; exact hh) 2]
include hp hQ h ht hV hv hM he
set_option linter.unusedSectionVars false in
lemma priceMark (hX:Nonwrapping X o)(hN:4 ≤ f.val)(hh:1≤k):
    let F:= (g.comp (bill S N) ∘ M); let Q:=Jive v*C
    0 ≤ Q∧ Ease.Charm R X F ∧ R.supBounds o X F (Q*fern L^3) ∧ ‖F 1‖ ≤ Q*fern L^5 ∧
       ∀ (i: Directions su f)(T:ℝ), Lyre.Sized T i R o → Mom.screen X i∈Mom.Maps o X 1 → ‖fderiv ℝ (F ∘ increment 1) 0 i‖ ≤ (T*K.fee)*Q*fern L^4 :=by
    intro F Q
    let y:= (g.comp (bill S N)); let a':= fern L; have ht':0<a':=fern_pos L
    have hp0:=hp.travel
    obtain ⟨h₀,hp₁,hp₂⟩:= virtue v
    have hL:0≤ Jive v:= h₀.trans hp₂
    have ha: Ease.Charm R X M:= ⟨hp.room,hp.use⟩
    have hF:=ha.scales y
    refine ⟨mul_nonneg hL hp0,hF,⟨by have hQ:0≤Q:=mul_nonneg hL hp0; positivity [fern_pos L],?_⟩,?_,?_⟩
    · intro U hU l hh hx; rw [left_linear _ _ (hp.use U hU) hh]; apply (he _).trans; refine (broad hQ h ht hV hv _ (leftovers hp hM.no U hU l hh)).trans ?_
      exact (mul_le_mul (mul_le_mul_of_nonneg_right hp₁ (pow_nonneg ht'.le _)) (hp.pole _ hU l hh hx) (norm_nonneg _) (by positivity [fern_pos L])).trans_eq (by unfold Q; ring)
    · apply (he (bill S N (M 1))).trans; have hx:= rebate hQ h ht hV hv _ (hM.no 1) (hM.flavor 1) (neon _ M (hM.flavor _) hM.gauge _ hM.heads)
      apply hx.trans; have hu: nickel L true =a'^5:=rfl; rw [hu]; exact (mul_le_mul (mul_le_mul_of_nonneg_right hp₂ (pow_nonneg ht'.le _)) (hp.sizeU _ (AnalyticBridge.VerifiedReset.flat_ok ..)) (norm_nonneg _) (mul_nonneg hL (pow_nonneg ht'.le _))).trans_eq (by unfold Q a'; ring)
    intro i T hk hr
    let f':= M ∘ increment (1:Grid f); have hs := hp.use (1:Grid f) (AnalyticBridge.VerifiedReset.flat_ok ..); have hI :1≤R.order:= le_trans (by norm_num) R.order_ge
    have hp : DifferentiableAt ℝ f' 0:= hs.differentiableAt (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hI): (R.order:WithTop ℕ∞)≠0)
    let z:= fderiv ℝ f' 0 i; let c:=clay f N|>.restrictScalars ℝ
    have hz : mud z=0:=by
       have he': c z= fderiv ℝ (c ∘ f') 0 i:= (congr_arg (fun x:Directions su f→L[ℝ] ℂ=> x i) ((c.hasFDerivAt (x:=f' 0)).comp 0 hp.hasFDerivAt).fderiv).symm
       change c z=0; rw [he',show (c ∘ f')=fun _=> 0 from funext fun i=> hM.no _]; simp
    have hx := dutyH M ha.sites hM.gauge hM.flavor hp hX hN b hM.heads i hr; have hh₁ : Sen o t z ≤ T*K.fee*C:=by
       have hp:=aural K (M:=M) (R:=R) (X:=X) (by assumption) 1 (AnalyticBridge.VerifiedReset.flat_ok ..) (fun _ : Fin 1=>i) (fun _=>T) hh hI (fun _=>hk); simpa only [iteratedFDeriv_one_apply,Fintype.prod_unique] using hp
    have he₀ : fderiv ℝ (F ∘ increment 1) 0 i=y z:= congr_arg (fun f:Directions su f→L[ℝ] ℝ=> f i) ((y.hasFDerivAt (x:=f' 0)).comp 0 hp.hasFDerivAt).fderiv
    rw [he₀]; apply (he (bill S N z)).trans; apply (rebate hQ h ht hV hv z hz (drip M hM.flavor hp _) hx).trans; have hu:nickel L false =a'^4:=rfl; rw [hu]; exact (mul_le_mul (mul_le_mul_of_nonneg_right hp₂ (pow_nonneg ht'.le _)) hh₁ (norm_nonneg _) (mul_nonneg hL (pow_nonneg ht'.le _))).trans_eq (by unfold Q a'; ring)
end YM.QCD.Dust
