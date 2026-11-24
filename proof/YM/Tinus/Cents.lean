import YM.Tinus.Rut
import YM.Tinus.Shuck
/-! parity signature under flavor flips. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical TensorProduct
variable {S:Scheme}{R c:Side}{d n i j:ℕ}
open Poised.Display Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Exposure
variable (x:Label d)
variable (a b:Flavor 6)
noncomputable def bandK (j:Flavor 6):ℝ:= if j=a then -1 else 1
noncomputable def ribbonK : FlavorTorus:= fun i=> ⟨(bandK a i:ℂ),by unfold bandK; split<;> constructor<;> simp⟩
local notation "P"=> ribbonK a
noncomputable def stockL (i:Pairs (SpinMode d)):ℝ:=bandK a (Sum.elim Prod.snd Prod.snd i)
local notation "W"=> UV.flavorAct (d:=d) P
lemma fresh : ((ribbonK a) : FlavorTorus)⁻¹ =P := by funext i; apply Subtype.ext; exact Complex.conj_ofReal (bandK a i)
lemma flavorB (i:PowerPair d) : W (gen i)=(∏ j∈ i.2, ((stockL a j):ℂ)) • gen i:=by
     unfold UV.flavorAct UV.gen; rw[TensorProduct.map_tmul,fresh,←TensorProduct.tmul_smul]; congr 1
     let T:=P; let Q:= Grass.mono i.2; change (adapter (byFlavor P fun i:SpinMode d=>i.2) (byFlavor P fun i:SpinMode d=>i.2)) Q = _
     rw [← show Creek.wscale (stockL a) (mono i.2)=_ from Creek.wscale_mono ..]
     unfold Creek.wscale adapter; refine AlgHom.congr_fun (congr_arg changeVars ?_) Q; ext (i|i) (j|j)<;>simp [byFlavor, ribbonK, stockL, Matrix.diagonal_apply]

lemma flash (p:Rings d): coord p.val (W x.val)=(∏ j∈ p.val.2, ((stockL a j):ℂ))*coord p.val x.val:=by
     suffices h : (coord p.val).comp W=(∏ j∈ p.val.2, ((stockL a j):ℂ)) • coord p.val from LinearMap.congr_fun h x.val
     apply (zBasis d).ext; intro i; rw [minted,LinearMap.comp_apply, flavorB,map_smul]; by_cases h:p.val=i
     · subst i; rfl
     rw [LinearMap.smul_apply]; rw [show coord p.val (gen i)=0 from ?_,smul_zero,smul_zero]; unfold coord; rw [← minted]; simp [h]
lemma darkens (h:W x.val=-x.val)(p:Rings d)(hp:coord p.val x.val≠0):∃ i∈ p.val.2, Sum.elim Prod.snd Prod.snd i=a:=by
     by_contra! h'; have hx:(∏ j∈p.val.2,(stockL a j:ℂ))=1:=prod_eq_one fun i hi=>by simp [stockL,bandK,h' i hi]
     have hQ:= flash x a p; rw [h,map_neg,hx,one_mul] at hQ; exact hp (neg_eq_self.mp hQ)
variable (x:Label 8)(h:a≠b)
include h
local notation "jP" j:arg=>ribbonK j
open Poised.Sieve
lemma thickness (hX:flavorAct (jP a) x.val= -x.val)(hY:flavorAct (jP b) x.val= -x.val) : Poised.Plans.Stamp.Stair.OffS x:=by
    refine ⟨fun j he=>?_⟩
    obtain ⟨u,hu,hau⟩:=darkens x a hX j he; obtain ⟨v,hv,hbv⟩:=darkens x b hY j he; have he:u ≠ v:=by intro q; exact h (hau.symm.trans (q ▸ hbv)) -- maybe h mismatch
    have hb: UV.weight j.val ≤ 8 :=(Set.Finite.mem_toFinset (weightFinite 8)).mp j.property
    let k:= j.val.1; let t:=j.val.2; have hx:#t*3≤ ∑ i∈t, letterWeight i:=by rw [show #t*3=∑ _i∈t,(3:ℕ) from (by simp)]; exact sum_le_sum fun i _=> Nat.le_add_right ..
    have hp':({u,v}:Finset (Pairs (SpinMode 8)))⊆t:=Finset.insert_subset hu (singleton_subset_iff.mpr hv); have hC:=card_pair he; have hf: #t ≤ 2:=by change 2*Labels.height k+(∑ i∈ t, letterWeight i) ≤ _ at hb; omega
    have hT:t={u,v}:=(eq_of_subset_of_card_le hp' (hf.trans_eq hC.symm)).symm
    have hm:= le_trans (show 2*Labels.height k+(∑ i∈t,letterWeight i) ≤ 8 from hb) le_rfl; rw [hT,hC] at hx; have ht:k=0:=by
         by_contra hP; obtain ⟨i,hi⟩:= Finsupp.support_nonempty_iff.mpr hP; have h:2 ≤ Labels.height k:=by
             unfold Labels.height; have hp:= single_le_sum (f:=fun i:Labels.Key su=> k i • Labels.generation i) (fun a _=> Nat.zero_le _) hi; change 2 ≤ ∑ i∈k.support, k i • Labels.generation i
             exact le_trans (b:=k i • Labels.generation i) (le_trans (Nat.le_add_left 2 i.1) (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)))) hp
         rw [hT] at hm; omega
    have hK:life k=0:=by rw [ht]; rfl
    have hz:UV.weight j.val=letterWeight u+letterWeight v:=by
         change 2*Labels.height k+(∑ i∈ t, letterWeight i)=_; rw[ht,hT,sum_pair he, show Labels.height (G:=su) 0=0 from map_zero _,mul_zero,zero_add]
    have hW: (crest j.val).2=(0,2):= Prod.ext hK ((congr_arg Finset.card hT).trans hC)
    have hq:UV.weight j.val=6 ∨ UV.weight j.val=8:=by unfold letterWeight spinWeight at hz; omega
    exact hq.elim (fun h=> Or.inl (Prod.ext h hW)) (fun h=>Or.inr (Prod.ext h hW))
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.thickness
