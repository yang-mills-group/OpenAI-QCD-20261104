import YM.Massive.Reservoir.Bare
import YM.Massive.Reference.Fly

/-!
# Actual → normal multi-scale Pixels

`Run.Actual` does not require continuity; it follows. No need for ad hoc
bend parameter choices here; link reflection, cut normalization, exact step
between all normalized pixels from `Actual`. In particular no pointwise
reality/positivity assumption on the gauge marginal of a run. Steps here at
constant scheme as in `Reference`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Lat QCD.Grass Lattice Wilson RG Function MeasureTheory QCD.Cove
open QCD.Tide QCD.Acre QCD.Acre.Rails QCD.Rain QCD.Acre.Rails.Reference
open scoped BigOperators Topology Matrix.Norms.L2Operator ComplexOrder
namespace Run
variable {n N F i : ℕ} {P : Patch} {K : KernelChoices} {R c : Side} {h:P.Branches K su} {S:Scheme}
variable (A:Run S N R F) (he : A.Actual)
noncomputable def paper (Z:Density c F):Pixel c F:= levit c F ∘ Z
lemma paper_lit {Z:Density c F}(he:∀ U,Plus (Z U)) : light _ ∘ paper Z= Z:= by
  funext U; let X:EvenA c F:=⟨Z U,he U⟩
  change light _ (levit c F (light _ X))= _; rw [callH]; rfl
lemma paper_back (Z:Pixel c F): paper (light _∘ Z)=Z:= funext fun _=>callH _

noncomputable def stock (i:ℕ) := paper (A.density i)
/-- Normalized active level. -/
noncomputable def state (i:ℕ): Pixel (S.side R i) F:= money (A.stock i)
/-- Actual `Stud` functional already normalized (need `Actual`, Stays or other integrable
conditions for additivity etc.). This has a value even for unproven hypotheses. -/
def visible (i:ℕ)(x:Stud (S.side R i) F) := Tide.fresh (A.state i) x

include he
lemma lit (hi:i ≤ N): Cove.light _ ∘ A.stock i = A.density i:=paper_lit (he.even hi)
lemma continuity (hi:i ≤ N): Continuous (A.density i):=by
    induction hi using Nat.decreasingInduction with
    | self => rw [he.start]; exact ContinuousMap.continuous _
    | of_succ k hk ih=> rw [he.travels.eqn (Nat.zero_le _) hk]; exact Transfer.continuous _ _ _ _ _ (S.admissible _) ih
lemma earned (hi:i ≤ N):0< Cvol (A.stock i):=by change 0< joint (light _ ∘ A.stock i); rw [lit A he hi]; exact he.normal hi
lemma volume_l (hi:i≤N): Cvol (A.stock i)=joint (A.density i):= by rw [← lit A he hi]; rfl -- nth_rw?
lemma standing (hi:i ≤ N): Continuous (A.state i) ∧ Cvol (A.state i)=1:=by
    let x:= Cvol (A.stock i); have h:= earned A he hi; let t:=x.re; have ht: (0:ℝ)<t:= (Complex.lt_def.mp h).1; have hp:(t:ℂ)=x:=Complex.ext (by simp [x,t]) (show _= _ from (Complex.lt_def.mp h).2)
    refine ⟨continuous_const.smul ((levit _ F).continuous.comp (continuity A he hi)),?_⟩; unfold state; rw [lucent]; change t⁻¹ • x= _; rw [← hp]; simp [ht.ne']
lemma visible_ratio (hi:i ≤ N)(x:Stud (S.side R i) F) : visible A i x = ((joint (A.density i))⁻¹:ℂ) * joint ((A.density i)*x):=by
    let c:=S.side R i; let u:=A.stock i; let Z:= Cvol u
    have hp: (Z.re:ℂ)=Z := Complex.ext (by simp [Z]) (show _= _ from (Complex.lt_def.mp (earned A he hi)).2)
    unfold visible state money; rw [journey];
    have hx:(A.state i)= Z.re⁻¹ • u:=rfl
    rw [← lit A he hi]; change (Z.re⁻¹) • joint ((light _ ∘ u)*x)= Z⁻¹*joint ((light _ ∘ u)*x); rw [Complex.real_smul,Complex.ofReal_inv,hp] -- complex cast

omit he
variable (T: Run (fixed P K h) N R F) (hp:T.Actual)
private lemma unscale {w:ℝ} (hw:0<w)(x:Fields c F) : rescale w⁻¹ (rescale w x)=x:=by
    classical
    unfold rescale; rw [← AlgHom.comp_apply, ← change_mul];
    let B (w:ℝ):Matrix (Pairs (Modes c F)) (Pairs (Modes c F)) ℂ:= Matrix.diagonal (fun _=>(w:ℂ)); change changeVars (B w*B w⁻¹) x=x; rw [show B w *B w⁻¹=1 from ?_,change_one]; rfl
    unfold B; ext i j; rw [Matrix.diagonal_mul_diagonal]; simp [Matrix.diagonal_apply,Matrix.one_apply,hw.ne']
private theorem warmed {Y: YM.Next.Free.Flight i i} {f c:Side} (h: f.val=c.val*Y.L.val)(K:KernelChoices)(β w:ℝ)(X:Pixel f F)(Z:Pixel c F) (he:0<w)(hx:Continuous X)(hp:Y.patch.Branches K su) (ht: light _∘Z = transfer Y K h β w (light _∘ X)) : Modern Y K h β w (money X) (money Z):=by
    have hV : Cvol Z= Transfer.growth c F w * Cvol X:=by
        change joint (light _ ∘ Z)= _ * joint (light _ ∘ X); rw [ht,Transfer.conserves (F:=F) Y K h β w hp _ (Transfer.soften_pay _ _ ((lightC _).comp hx))] -- arg f
    apply moved Y h X Z w _
    · intro i; have ht: light _ (Z i)= rescale w (advance Y K h X β i):= congr_fun ht i; change _= rescale w⁻¹ (light _ (Z i)); rw [ht]; exact (unscale he _).symm
    rw [hV,Complex.real_smul]; have hh:Transfer.growth c F w≠0:=Ne.symm ((pow_pos (Complex.zero_lt_real.mpr he) _).ne); -- orientation .ne
    rw [show (Rain.gain w⁻¹ c F:ℂ)=(Transfer.growth c F w)⁻¹ by unfold Rain.gain Transfer.growth; push_cast; rw [inv_pow] , inv_mul_cancel_left₀ hh]
include hp
lemma active_step (hi : i<N): Modern (Pike P 0) K ((fixed P K h).sides_next R i) (T.β (i+1)) (T.w i) (T.state (i+1)) (T.state i):=by
    let H:= hp.travels.eqn (m:=i) (Nat.zero_le _) hi
    apply warmed (Y:=Pike P 0) _ K _ _ (stock T (i+1)) (stock T i) (hp.w_pos hi) ((levit _ _).continuous.comp (continuity T hp hi)) h
    rw [lit T hp hi.le, (show light _ ∘ T.stock (i+1) =_ from lit T hp (show i+1≤N from hi))]; exact H
/-- Reflection positivity on every level. Need even period to be used
(existence of link cuts with half-width at least two). -/
lemma state_health (hi:i ≤ N) : Healing P (T.state i):=by
   induction hi using Nat.decreasingInduction with
   | self=> refine Regulator.base_health (R:=T.regulator) _ _ (earned T hp le_rfl) ?_ rfl ((show 0<T.β N from hp.beta_pos le_rfl).le); exact (lit T hp le_rfl).trans hp.start
   | of_succ k hk ih=> exact Tide.health (Pike P 0) _ h _ _ ih (hp.w_pos hk) (T.standing hp hk).1 (active_step T hp hk)
end Run
end YM.Massive
#print axioms YM.Massive.Run.state_health
