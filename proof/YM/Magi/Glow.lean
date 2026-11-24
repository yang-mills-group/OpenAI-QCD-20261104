import YM.Cape.Arch
import YM.Rebus.Vent
import YM.Magi.Town
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open Function Lattice RG Pressure MeasureTheory Finset QCD Kites Kit Port Flume
open Grass Lat Play QCD.Bera
open Stitch Plate Loom Loom.Fleet Sway OrbitG Ribbon Rebus Creek Cove Apron Apron.Grove Cupola QCD.Acre QCD.Acre.Rails
open Anomaly
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{N:ℕ}{I D Z U J R:Type} [Fintype I] {l φ k B P A A':ℕ} {v α s t:ℝ}
local notation "F0"=> (Keys c N)
open QCD.Brick QCD.Dust -- edit
-- payload color for actual evaluator. does not insert new face handshake.
namespace LampV
def fuelColor (N:ℕ):ℝ:= max 1 (↑(stemF N):ℝ)
variable (N)
def engineP (V:Lat.Frame c): Matrix (Keys c N) (Keys c N) ℂ := Matrix.fromBlocks (Lat.rotates N V) 0 0 (star (Lat.rotates N V))ᵀ
lemma unitsP (g:Lat.Frame c)(i j:Keys c N): ‖engineP N g i j‖ ≤1:=by
     have hv:= rotates_law N g
     rcases i with i|i <;>rcases j with j|j
     · exact (Cost.north (rotates N g) i j).trans (Lat.rotation_price hv)
     · exact norm_zero.le.trans zero_le_one
     · exact norm_zero.le.trans zero_le_one
     exact (Cost.north (star (rotates N g)) _ _).trans (Lat.rotation_price (Unitary.star_mem hv))
lemma awayP (g:Lat.Frame c)(i j:Keys c N)(h: locationP i≠ locationP j) : engineP N g i j =0:=by
     have hx(i j:Modes c N)(he:i.1.1≠j.1.1): rotates N g i j=0:=by unfold Lat.rotates copies siteRot; rw [Matrix.blockDiagonal_apply]; split; exact if_neg he; rfl
     rcases i with i|i <;>rcases j with j|j
     · exact hx _ _ h
     · rfl
     · rfl
     change star ((rotates N g) i j)=_; rw [hx i j h,star_zero]
lemma payW (g:Lat.Frame c): bills (engineP N g) univ (fuelColor N):=by
     intro i _; let s:=limits (F:=N) ({locationP i}); rw [←sum_subset (s₁:=s) (subset_univ s) (fun j _ hj=>?_)]
     swap; · rw [awayP _ _ _ _ (fun k=> hj (show j∈limits (F:=N) {locationP i} from mem_filter.mpr ⟨mem_univ _,mem_singleton.mpr k.symm⟩)), norm_zero]
     apply (sum_le_sum (g:=fun _=>1) (fun i _=> unitsP ..)).trans; rw [sum_const]; unfold s; simp only [nsmul_eq_mul,mul_one]; rw [leapX]; exact le_max_right ..
lemma raiseH {A B U:Type}[Fintype A][Fintype B][Fintype U][DecidableEq U](F:Matrix A B ℂ) (h:bills F univ s)(hp:1 ≤ s): bills (breezeP U F) univ s:=by
     intro i _
     rcases i with x|x
     · rw [Fintype.sum_sum_type]; simp only [breezeP,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,norm_zero,sum_const_zero,add_zero]; exact h _ (mem_univ _)
     rw [Fintype.sum_sum_type]; simp only [breezeP,Matrix.fromBlocks_apply₂₁,Matrix.zero_apply,Matrix.fromBlocks_apply₂₂,norm_zero,sum_const_zero,zero_add]; rw [sum_eq_single x]; simp only [Matrix.one_apply_eq,norm_one]; exact hp; intro b hb hB; rw [Matrix.one_apply_ne (Ne.symm hB),norm_zero]; simp
set_option maxHeartbeats 800000 in
lemma stamped (k:ℕ)(g: Lat.Frame c)(x:Patio ((Keys c N)⊕ Ribbon.Spine I))(h:x.val ∈ Anomaly.Rim univ k): ‖parcelColor N g I x‖ ≤ fuelColor N^k *‖x‖:=by
      let f:= Lat.rotates N g; let p:= engineP N g
      let U:=(parcelColor N g I x).val
      have hu: U= (Ribbon.carry (Spine I) (Lat.slots N g).toLinearMap.toContinuousLinearMap) x.val:= rfl
      have hg: changeVars p=Lat.slots N g:=rfl
      have ht: U = changeVars (Anomaly.breezeP (Spine I) p) x.val:=by rw [Anomaly.shipsT,hg]; exact hu
      have he:1 ≤ fuelColor N:= le_max_left ..
      change ‖U‖ ≤ _; rw [ht]
      exact Anomaly.sendsTotal (Anomaly.breezeP (Spine I) p) h (raiseH p (payW N g) he) he
-- value card credits `cost Amount pad`: just bounded degree.Load constraint. no amp for gauge.W.V.Weak.
lemma warmP {I:Type}[Fintype I] (C:ℕ)(g:Patio ((Keys c N)⊕ Ribbon.Spine I))(h:g.val∈ Anomaly.Rim univ C)(ht:1 ≤ v): Tablet.credits v g ≤ v^C*‖g‖:=by
     have hP:0≤ v:= zero_le_one.trans ht; let f: Keys c N⊕ Ribbon.Spine I→ℝ:=Stitch.Tablet.chip v _ _
     change load f g.val ≤ v^C*‖g.val‖; rw [Creek.dry f (fun x=> by cases x; exact zero_lt_one.trans_le ht; exact zero_lt_one),Grass.norm_def,Finset.mul_sum]; -- inspect
     refine sum_le_sum ?_; intro i _; by_cases h': coef i g.val ≠0
     · have hi:= h i h'; change _* ‖coef i g.val‖≤ _
       apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); apply le_trans ?_ (pow_le_pow_right₀ ht hi.2)
       simpa only [Finset.prod_const] using! (Finset.prod_le_prod (g:=fun _=>v) (f:= f) (s:=i) (fun x _=> by cases x; exact hP; exact zero_le_one) (fun x _=>by cases x; exact le_rfl; exact ht)) -- order load?
     push Not at h'; rw [h',norm_zero,mul_zero,mul_zero]
end LampV
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.LampV.stamped
#print axioms YM.MassiveQCD.Cape.LampV.warmP
