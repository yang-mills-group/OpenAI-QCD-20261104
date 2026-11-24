import YM.QCD.Smoke.Stack

/-! # funds at fixed ratio and tower, including arbitrary narrower postprices. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {E:Patch} {j k N B:ℕ}{K:KernelChoices}{p:Clip}{r D A u v Λ δ c Y w q g R:ℝ}{M: Before su u v E.J K N}
-- chimney from any given graph
variable (V:Back E K j k p u v)(J:Plan j){U:On}
def scent (T:On)(w:ℝ)(i:ℕ)(z:Site (V.chain.n i)):= chimney w J (V.port.forest i) (T _) (V.port.u i) z -- syntax
lemma scented (T:On)(hU:Vital T)(w:ℝ)(i:ℕ)(z:Site (V.chain.n i))(F:Forest (anchor V i).ratio)(t:Bid.Dir su _→AxisChart su F)(hh:Critical F p V.path t): scent V J T w i z=ᶠ[𝓝 0] chimney w J F (T _) t z:= sun_public hh (V.port.admiss i) V.port.paid (hU.1 _) w J (V.port.critical i) _
lemma forestP (M:Before su u v E.J K N) i : ∃ x,M.Service (V.port.forest i) p V.path x:= Before.graph (S:=anchor V i) _ M V.port.paid (V.port.admiss i) (congr_arg Patch.J V.origin) rfl

def creditP (E:Patch)(r D:ℝ):= (Fintype.card (Site E.L):ℝ)*(Fintype.card Fiber:ℝ)*(D * Real.exp (r*E.L.val)^2)
lemma credit_nn (E: Patch)(r)(ht:0 ≤ D):0≤ creditP E r D:=by unfold creditP; positivity

variable (hp:Arbor J E.L k 1 w q g R δ Y B) (hU:Vital U)(hr:0<r)(he:0≤D)(h:Plume V J M U r D w)
-- down embeddings
lemma slant {s n:Side}(g:Ratio s n)(x y:Site s)(hp:0 ≤ r) : Decay r (g.embed x) (g.embed y) ≤ Decay r x y:= by
  unfold Decay; apply Real.exp_monotone; rw [Next.Rank.Station.both]; push_cast; have ht:(1:ℝ)≤g.count.val:=by exact_mod_cast g.count.property
  exact mul_le_mul_of_nonpos_left (le_mul_of_one_le_left (by positivity) ht) (neg_nonpos.mpr hp)
include hU hr he h
lemma revenueP (i:ℕ)(z:Site (V.chain.n i)): Flock (traceG (V.chain.n i)) Push.Uniform.bolt (scent V J U w i z) z r (creditP E r D):=by
  let S:=anchor V i; let ρ:=S.ratio; let m:= V.chain.n i
  obtain ⟨x,hx⟩:=forestP V M i
  apply Flock.aliasG _ (scented V J U hU w i z _ x hx.critical)
  let Z:=quilt V J w U i (V.port.forest i) x; let W(j:Site ρ.count):=ρ.assemble (z,j)
  let B:= D*Real.exp (r*E.L.val)^2; let A(u:Cnr m)(i:Site ρ.count)(k:Fiber):= (Z u ((W i),k) ((W i),k)).re
  have hL : ρ.count=E.L:= V.has
  have h' (y:Site ρ.count)(k:Fiber): Flock (traceG m) Push.Uniform.bolt (fun i=> A i y k) z r B:=by
    let b:Row (localG V i):= (W y,k); let f(t:Cnr m):=Z t b b; have hQ: Flock (beam ρ) Push.Uniform.bolt f (W y) r (D*Decay r (W y) (W y)):= h _ _ _ hx b b
    have he : separation (ρ.embed z) (W y) ≤ E.L.val:=by
      have ht:= Corona.near ρ (ρ.assemble (z,y)); rw [ρ.assemble_parent] at ht; change 2*separation (W y) (ρ.embed z)≤ρ.count.val at ht; rw [separation_comm,hL] at ht; omega
    have hp: Flock (beam ρ) Push.Uniform.bolt f (ρ.embed z) r B:=by
      apply (hQ.roster (ρ.embed z)).patron
      rw [Decay,separation_self]; simp only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one,Decay]; rw [← Real.exp_neg,neg_mul, neg_neg]; unfold B; gcongr
    let L:=Complex.reCLM
    have hu (c:ℂ): ‖L c‖≤‖c‖:=Complex.abs_re_le_norm _
    change Flock _ _ (L ∘ f) _ _ _; refine ⟨hr,hp.fee,L.contDiff.contDiffAt.comp 0 hp.host,(hu _).trans hp.born,fun j=>?_,fun j k=>?_⟩
    · rw [retell _ _ hp.host]; exact ((hu _).trans (hp.walks j)).trans (mul_le_mul_of_nonneg_left (slant ρ z (traceG m j) hr.le) hp.fee)
    rw [retold _ _ L hp.host]; exact ((hu _).trans (hp.wandered j k)).trans (mul_le_mul_of_nonneg_left (mul_le_mul (slant ρ z (traceG m j) hr.le) (slant ρ z (traceG m k) hr.le) (decay_pos ..).le (decay_pos ..).le) hp.fee)
  have hh : chimney w J (V.port.forest i) (U _) x z=(fun t:Cnr m=> -(∑ j:Site ρ.count,∑ f:Fiber,A t j f)):=funext fun i=>congr_arg Neg.neg (sum_congr rfl fun j _=>Complex.re_sum _ _)
  rw [hh]; apply Flock.nu; have hv:= Flock.convoy (s:=univ) hr fun i _=> Flock.convoy (s:=univ) hr (fun j _ => h' i j)
  simp only [sum_const, card_univ, nsmul_eq_mul] at hv; apply hv.patron; rw [hL,mul_comm]; unfold creditP B; linarith -- inspect
include hp
lemma modestP {i j':ℕ}(hh:i≤j')(x: Site (V.chain.n j')) (a b : Cnr (V.chain.n i)) :
    let L:= V.chain.vista i j' hh
    ‖Jacobi.mixed a b (scent V J U w i (L.cut x)) 0-Jacobi.mixed (expandC L a) (expandC L b) (scent V J U w j' x) 0‖≤ (Fintype.card (Site E.L):ℝ) * lantern (seedG r D*‖a‖*‖b‖) r *Real.exp (-(r/2)*(localG V i).val):=by
  intro L
  obtain ⟨t,hz⟩:=forestP V M i
  obtain ⟨F,v,d,hy,hk,Ht⟩:=wind_cut V J M hh (V.port.forest i) t hz U hU hp
  have hM := h j' _ _ hy
  rw [repeated _ _ (scented V J U hU w i (L.cut x) _ _ hz.critical),repeated _ _ (scented V J U hU w j' x F v hy.critical),← V.has]
  exact roll_out (Z:=quilt V J w U j' F v) _ x hk Ht hr he hM (matrix_g fun j k=>(h _ _ _ hz j k|>.host)) a b
end YM.QCD.Smoke
