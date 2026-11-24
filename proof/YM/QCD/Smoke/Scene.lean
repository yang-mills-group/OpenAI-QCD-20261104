import YM.QCD.Smoke.Steady

/-! # log power budgets assembled after arbitrary lifted forest -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Function Filter Finset Lat Cost Run Eyrie Metric Lattice Wilson Push.Uniform
open YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Matrix BigOperators Topology ContDiff Classical Matrix.Norms.L2Operator
variable {n:Side}{X V:Type} [NormedAddCommGroup X][NormedSpace ℝ X] {A C R r w D u q g:ℝ}{U:ℕ→ℝ} {l:V→ Site n}{k:V→X}{p:Row n→Site n}

def tallyG (U:ℕ→ℝ)(r B:ℝ)(q:ℕ)(i:ℕ):= U i + fuseG U U r B q i + fuseG U (fuseG U U r B q) r B q i
def walletG (U:ℕ→ℝ)(r C:ℝ)(q:ℕ)(i:ℕ):=4* (‖((i+1:ℂ))⁻¹‖*tallyG U r C q (i+1))
lemma coverG (h:0<r)(hy:0≤C)(he:∀ i,0≤ U i)(q:ℕ):∀ i, 0≤ walletG U r C q i:=by
  intro i; unfold walletG; apply mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) _); exact add_nonneg (add_nonneg (he _) (fuseP _ _ he he _ hy h _)) (fuseP _ _ he (fuseP _ _ he he q hy h) q hy h _)
lemma totalsG (h:0<r) (hy:0 ≤C)(he:∀ i,0 ≤ U i)(ha:Summable U)(q:ℕ): Summable (walletG U r C q):= by
  have hx: Summable (tallyG U r C q):= (ha.add (fuses ha ha)).add (fuses ha (fuses ha ha))
  have hh (i:ℕ): walletG U r C q i ≤ 4*tallyG U r C q (i+1):=by
    have hp : ‖(i+1:ℂ)⁻¹‖≤1:=by rw [norm_inv,show ‖(i+1:ℂ)‖= (i+1:ℝ) by norm_cast]; exact inv_le_one_of_one_le₀ (by simp)
    apply mul_le_mul_of_nonneg_left ?_ (by norm_num); apply mul_le_of_le_one_left ?_ hp; exact add_nonneg (add_nonneg (he _) (fuseP _ _ he he _ hy h _)) (fuseP _ _ he (fuseP _ _ he he q hy h) q hy h _)
  exact (((summable_nat_add_iff 1).2 hx).mul_left _).of_nonneg_of_le (coverG h hy he q) hh
lemma broad {q:ℕ}(hq:Multiplicity p q)(hp:0<r)(ht:4*(4*r) ≤ u)(hh:Summable U)(hs:∀ i,0≤U i)(hC:0≤C)(F:X→Sheet n)
    (hw:‖F 0‖<1)(h:glyph l k p p F u C)(he:∀ i (x y:Row n), ‖((F 0)^i) x y‖≤ U i*Decay u (p x) (p y)): glyph l k p p (lap ∘ F) r (∑' i,walletG U r (C+C) q i):=by
  have hv:0<u:=lt_of_lt_of_le (by positivity) ht
  let Z:=fun _:X=> F 0
  let d:= F - Z
  have hD:0 ≤ C+C:=by linarith
  have hr : glyph l k p p d (4*r) (C+C):=by
    rw [show d=F+-Z from sub_eq_add_neg ..]; apply (glyph.plus h _).reduces (show 0<4*r by positivity) (by linarith) hD le_rfl; exact glyph.minus (C:=C) fun i j=> (Flock.hush _ hv).patron (h i j).born
  have hy (i:ℕ): glyph l k p p (Z^i) u (U i):=by
    intro x y; simp only [Pi.pow_apply]; exact (Flock.hush _ hv).patron (he i x y)
  have hj (i:ℕ): glyph l k p p (Z^i) r (U i):= (hy i).reduces hp (by linarith) (hs i) le_rfl
  let W (i:ℕ):= Z^i
  have hZ:=gusts (B:=W) q hq hp ht hs hs hD hy hr hj
  have hx:=gusts q hq hp ht hs (fuseP U U hs hs q hD hp) hD hy hr hZ
  have hM:ContDiffAt ℝ ω F 0:=matrix_g fun i j=>(h i j).host
  apply bunch _ hw hM hp ?_ (totalsG hp hD hs hh q)
  intro i; have he' := approximate F hM (i+1)
  have hg: glyph l k p p (F^(i+1)) r (tallyG U r (C+C) q (i+1)):= he'.redraw (((hj (i+1)).plus (hZ (i+1))).plus (hx (i+1)))
  simpa only [Pi.pow_apply,glyph,Pi.neg_apply,Pi.smul_apply] using! (hg.tariff ((i+1:ℂ)⁻¹)).minus

variable {T:Type*}{P: Works T}{K: RG.KernelChoices}{G:RG.Patch}{b:RG.Clip}{N B j t:ℕ}{Y δ a Λ:ℝ}{M:Before su a Λ G.J K N}
open Orbit Birth RG Flume Pine YM.Next.Free Quarry
variable (E:Quay P K G b M)(W:Plan j)(F:T→ Flight j t)(hf: ∀ i,(F i).patch=G)
lemma league_log {U : (y:T)→ Grid (P.n y)→Sheet (P.n y)} (hp: Arbor W G.L t 1 w q g R δ Y B)(h:P.League (A:=true) (B:=true) fun y x=> U y (E.forge y x))(he:∀ i, U i 1=0):
    P.League (A:=true) (B:=true) (fun y x=>lap (notch w (shiftH (F y) (E.ratio_info hf y) W (U y) (E.forge y x)))):=by
  have H : P.League (A:=true) (B:=true) (fun i x=> notch w (shiftH (F i) (E.ratio_info hf i) W (U i) (E.forge i x))):= (Works.League.identity ..).down (Works.League.tax ((E.referee hf W).plus h) _)
  obtain ⟨r,C,hr,hC,H⟩:=H; have hu := lt_min hr (amplitude_pos B); let d:= min r (amplitude B); let e:= d/16; have hz:0<e:=by unfold e; positivity
  let V (i:ℕ):= R*g^i; let ν:= Fintype.card Fiber
  have hV:Summable V:= (summable_geometric_of_lt_one hp.pays.le hp.grade).mul_left R; have hv i:0≤V i:=mul_nonneg hp.solid.le (pow_nonneg hp.pays.le _)
  refine ⟨e,∑' i,walletG V e (C+C) ν i,hz,(tsum_nonneg (coverG hz (add_nonneg hC hC) hv ν)),fun i=>?_⟩
  let A : Cnr (P.s i)→Sheet (P.n i):=fun x=> notch w (shiftH (F i) (E.ratio_info hf i) W (U i) (E.forge i x))
  have ha: A 0= notch w (vaultF W (F i) (E.ratio_info hf i) 0 1) :=by unfold A shiftH; rw [E.forge0,he,add_zero]
  have ht:= hp.uses (F i) (E.patches hf i) _ _ (E.ratio_info hf i) B le_rfl 0
  change glyph (beam (P.ratio i)) Push.Uniform.bolt Prod.fst Prod.fst (lap ∘ A) e _
  refine broad (F:=A) (n:=P.n i) (p:=fun x:Row (P.n i)=>x.1) (multIF _) hz (show 4*(4*e)≤d by unfold e; linarith) hV hv hC ?_ ?_ ?_
  · rw [ha]; exact (ht.2.1 1).trans_lt hp.ceil
  · exact (H i).reduces hu (min_le_left ..) hC le_rfl
  intro j x y; rw [ha]; refine le_trans (purchases (ht.2.2 j) hp.tube x y 1) ?_
  exact mul_le_mul_of_nonneg_left (white (min_le_right ..) _ _) (hv _)
end YM.QCD.Smoke
