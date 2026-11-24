import YM.Massive.Pressure.Triangle
import YM.SectorNext.VACUUM_NORMALIZATION.Noise

/-!
# From **point** (flat) read to pressure lower

Haar-tree smoothing, needs a positive invariant marginal. No derivative of density.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure.Average
open Lattice RG Wilson Function SectorNext.Vacuum SectorNext.Vacuum.Masts MeasureTheory Filter Finset Tree
open Triangle (ranking wrap_inverse law peel kick_off kick_at)
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical ENNReal
variable {n f : Side} (hn : 1<n.val) (G : Gauge)
local notation "K"=> (Site n → G.El)

-- integrate tree over kicks at tips rather than splitting the Measure.pi.
def bud (e : Link n) : Site n := e.1+step e.2
abbrev Twig (n : Side) (hn : 1<n.val) := ↥((main n hn).trunks)
lemma twig (e : Twig n hn) : bud (n:=n) e.val≠0 ∧ e.val = (bud (n:=n) e.val - step (highest (bud (n:=n) e.val)),highest (bud (n:=n) e.val)):=by
  obtain ⟨x,hx,he⟩:= ((main n hn).trunk_mem_iff _).mp e.property
  change (x-step (highest x),highest x)=e.val at he; simp_rw [← he, bud, sub_add_cancel]
  exact ⟨(reachable x).mp hx,trivial⟩
lemma shallow (e : Twig n hn) : depth e.val.1 < depth (bud (n:=n) e.val):=by
  let X:= bud (n:=n) e.val
  have he : e.val.1 = X-step (highest X):= congr_arg Prod.fst (twig hn e).2
  exact he.symm ▸ Nat.lt_of_succ_le (shorten hn _ _ (highest_on _ (twig hn e).1)).le
lemma berry_cont (V : Config G n) : Continuous fun k : K => Lattice.gauge k V:=by unfold Lattice.gauge; fun_prop

variable (β : ℝ) (S : StepData n f) (hb : 0≤β)
def bill (Q V : Config G n) (e : Link n) (k : K) := (S.penaltyZ β G)⁻¹ * S.penaltyWeight β ((gauge k V) e * (Q e)⁻¹)
lemma bill_nonneg (Q V : Config G n) (e : Link n) (k : K) : 0 ≤ bill G β S Q V e k:=mul_nonneg (inv_pos.mpr (S.penaltyZ_pos β)).le (Real.exp_pos _).le
@[fun_prop] lemma bill_cont (Q V : Config G n) (e : Link n) : Continuous (bill G β S Q V e):=by 
  have hu := berry_cont G V
  unfold bill; apply Continuous.const_mul; exact (S.penaltyWeight_cont β).comp (((continuous_apply e).comp hu).mul (continuous_const (y:=(Q e)⁻¹)))
lemma bill_one (e : Twig n hn) (k : K) (Q V : Config G n) :
    (∫ u, bill G β S Q V e.val (Triangle.kick G (bud (n:=n) e.val) u k) ∂G.probHaar)=1:=by
  have h : e.val.1≠bud (n:=n) e.val:=by intro hf; exact (shallow hn e).ne (congr_arg depth hf)
  simp only [bill, Lattice.gauge,kick_off _ _ _ _ h, show _ + step e.val.2 = bud (n:=n) e.val from rfl, Triangle.kick_at,mul_inv_rev]; -- check
  rw [integral_const_mul];
  have he : ∀ u:G.El, k e.val.1*V e.val*((k (bud (n:=n) e.val))⁻¹*u⁻¹)*(Q e.val)⁻¹ = (k e.val.1*V e.val*(k (bud (n:=n) e.val))⁻¹)*u⁻¹*(Q e.val)⁻¹:=fun u=>by simp only [mul_assoc]
  simp_rw [he]; rw [wrap_inverse,←StepData.penaltyZ,inv_mul_cancel₀ (S.penaltyZ_pos _).ne']

lemma preserve {e d : Twig n hn} (he : e≠d) (hp : depth (bud (n:=n) d.val) ≤ depth (bud (n:=n) e.val)) (Q V : Config G n) (u) (k : K) :
    bill G β S Q V d.val (Triangle.kick G (bud (n:=n) e.val) u k)= bill G β S Q V d.val k:=by
  have hd : bud (n:=n) d.val≠ bud (n:=n) e.val:=by
    intro hx; apply he; apply Subtype.ext; exact (twig hn e).2.trans ((by rw [← hx]; exact (twig hn d).2.symm)) -- motive
  have hk : d.val.1 ≠ bud (n:=n) e.val:=fun hh=> ((shallow hn d).trans_le hp).ne (congr_arg depth hh)
  simp only [bill, Lattice.gauge, show _ + step d.val.2 = bud (n:=n) d.val from rfl,kick_off _ _ _ _ hd,kick_off _ _ _ _ hk]

lemma branch (Q V : Config G n) :
    (∫ k : K,(∏ i ∈ (main n hn).trunks,bill G β S Q V i k) ∂law G (Site n))=1:=by
  simp_rw [fun k=>(prod_coe_sort (main n hn).trunks fun i=> bill G β S Q V i k).symm]
  rw [show (∫ k : K,(∏ i:Twig n hn,bill G β S Q V i.val k) ∂ law G (Site n))= _ from Triangle.triangle G (fun i : Twig n hn => depth (bud (n:=n) i.val)) (fun i k=> bill G β S Q V i.val k)
    univ (fun i=>bud (n:=n) i.val) 1 (fun i=> bill_cont ..) (fun _ k=>bill_one ..) (fun i j h hp u k=>preserve hn G β S h hp _ _ _ _),one_pow]; -- equality

lemma noise_cont (Q V : Config G n) : Continuous fun k : K => S.noise β Q (gauge k V):=by
  change Continuous ((fun p : Config G n × Config G n => S.noise β p.1 p.2) ∘ fun k:K=> (Q,gauge k V))
  exact (S.noise_cont β).comp (continuous_const.prodMk (berry_cont G V))

include hb hn
lemma noise (Q V : Config G n) : (∫ k:K,S.noise β Q (gauge k V) ∂law G (Site n)) ≤ ((S.penaltyZ β G)⁻¹)^spare n := by
  let Z:=(main n hn).trunks; let v := (S.penaltyZ β G)⁻¹; let g := v^spare n
  let F (k:K) := ∏ i ∈ Z, bill G β S Q V i k; let l (k:K):= S.noise β Q (gauge k V)
  have hh : Continuous l:= noise_cont G β S Q V; have he: Continuous F:= continuous_finsetProd _ (fun i _=> bill_cont G β S Q V i)
  have hv : 0 ≤ v:=(inv_pos.mpr (S.penaltyZ_pos _)).le
  have hp : ∀ k, l k ≤ F k * g := by
    intro k; unfold l StepData.noise; change ∏ i:Link n, bill G β S Q V i k ≤ _
    rw [← Finset.prod_mul_prod_compl Z]; apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _=> bill_nonneg ..)
    rw [show g=∏ _i ∈ Zᶜ,v from ?_]
    · refine Finset.prod_le_prod (fun _ _=>bill_nonneg ..) (fun i hi=>?_)
      refine mul_le_of_le_one_right hv (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith : -β ≤0) S.kernel.penalty_pos.le) (Gauge.price_range ..).1))
    rw [Finset.prod_const, card_compl, ←show spare n = Fintype.card (Link n)-Z.card from ?_]
    · have he := Triangle.main_card hn; unfold Z; omega
  change (∫ k,l k ∂_) ≤ g; refine (integral_mono (hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ((he.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hp).trans_eq ?_
  change (∫ k,F k*g ∂ law G (Site n))=g
  rw [integral_mul_const, show (∫ k,F k ∂ law G (Site n))=1 from branch hn _ _ _ _ _, one_mul] -- reducible lambda Pi.mul

variable (hk : S.patch.Branches S.kernel G)
include hk hn
lemma density (U : Config G f) (V : Config G n) : (∫ k:K, S.density β U (gauge k V) ∂ law G (Site n)) ≤ ((S.penaltyZ β G)⁻¹)^spare n:=by
  unfold StepData.density; rw [integral_finsetSum]; simp_rw [integral_const_mul]; apply (sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (noise hn G β S hb (S.prediction U i) V) (S.likelihood_pos ..)).trans_eq _; rw [←sum_mul,S.chosen hk,one_mul]
  intro i _; exact ((noise_cont G β S (S.prediction U i) V).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _

/-- Generic smoothing. It's ok that evaluating the push is very point specific
(e.g. use `V=1`). Number of noise-edge normalizations in the price is only the
reduced #edges after tree retention. -/
theorem smooth (F : Config G f → ℝ) (hf : Integrable F (prior G f)) (hz : ∀ x,0≤F x)
    (hF : GaugeInvariant (S.push β F)) (V : Config G n) : S.penaltyZ β G ^ spare n * S.push β F V ≤ ∫ x, F x ∂prior G f:=by
  let w (x : Config G f) (k : K) := S.density β x (gauge k V) * F x
  have hi : Integrable (uncurry w) ((prior G f).prod (law G (Site n))):=by
    obtain ⟨C,hC⟩:= S.density_bound hk β; let g (p:Config G f × K):= S.density β p.1 (gauge p.2 V)
    have hp : Measurable g:= by
      let k (p:Config G f × K) : Config G f × Config G n:= (p.1,gauge p.2 V)
      have hh : Measurable k:=measurable_fst.prodMk ((berry_cont G V).measurable.comp measurable_snd)
      change Measurable ((fun x:Config G f × Config G n=> S.density β x.1 x.2) ∘ k)
      exact (S.density_meas hk β).comp hh
    exact (hf.comp_fst (law G (Site n))).bdd_smul C hp.aestronglyMeasurable (Eventually.of_forall fun p=> (Real.norm_of_nonneg (S.density_positive _ _ _)).trans_le (hC p.1 _))
  let Z := ∫ k,(∫ U, w U k ∂prior G f) ∂law G (Site n)
  have he(k:K):(∫ U, w U k ∂prior G f)= S.push β F V:=hF k _
  have hg : Z=S.push β F V:=by unfold Z; simp_rw [he]; simp
  rw [← hg]; let g:=S.penaltyZ β G ^ spare n; have hp := pow_pos (S.penaltyZ_pos β (G:=G)) (spare n); have hu : Z ≤ g⁻¹*∫ x,F x ∂prior G f:=by
    unfold Z; rw [← integral_integral_swap hi,← integral_const_mul]; apply integral_mono hi.integral_prod_left (hf.const_mul _)
    intro x; dsimp only [uncurry,w]; rw [integral_mul_const]; refine mul_le_mul_of_nonneg_right ?_ (hz x); unfold g; rw [← inv_pow]; exact density hn _ _ _ hb hk x V
  exact le_trans (mul_le_mul_of_nonneg_left hu hp.le) (by rw [←mul_assoc,mul_inv_cancel₀ hp.ne',one_mul])

end YM.Massive.Pressure.Average
#print axioms YM.Massive.Pressure.Average.smooth
