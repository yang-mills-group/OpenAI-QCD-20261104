import YM.Pollen.Oak
import YM.Eole.Rate
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
namespace Gain
open QCD.GasP
local notation "m"=> Keys c 6
local notation "G"=> Grid c
local notation "P"=>Patio (m⊕Spine I)
variable {t u v x b w γ:ℝ}{U:BudgetPoint}
variable (q:I→Bool) (o:I→Site c)(F: Rail c (ample 6 I) K) (W:I→ℝ)
-- support augmentation one halo per atom
variable (S:Support c)(k:ℕ) (a:Finset I)
abbrev armsZ (S:Support c)(a:Finset I):= S ∪ a.biUnion (fun i=> halo k {o i})
set_option quotPrecheck false
local notation "Y"=> armsZ o k
lemma size_gain (hp:a⊆ barn o S)(B: ℕ)(hv:0<B) : coverNumber B (armsZ o k S a)≤ coverNumber B S+a.card*(k+k+1)^4:=by
    induction a using Finset.induction_on with
    | empty=> simp[armsZ]
    | insert i a hi ih=>
       let s:= S; let f :=halo k {o i}; let h':= armsZ o k S a; have hz:o i∈S:= (inside ..).1 (hp (mem_insert_self ..)); have hS:o i∈ f:=halo_subset k _ (mem_singleton_self _); have hh :=Corona.meets_sum (show o i∈ h' from mem_union_left _ hz) hS B; have hk: coverNumber B f ≤ _:= (Corona.cover_mono (show f⊆ halo (k*B) {o i} from Corona.halo_mono (Nat.le_mul_of_pos_right _ hv) le_rfl) _).trans (Corona.tile (o i) k B hv)
       have hq: a⊆ barn o S:= (subset_insert ..).trans hp
       rw [card_insert_of_notMem hi, armsZ, Finset.biUnion_insert, add_mul,one_mul,show S ∪ _=h'∪f from ?_]; · exact (hh.trans (Nat.add_le_add (ih hq) hk)).trans_eq (Nat.add_assoc ..)
       unfold h'; rw [union_comm f,← union_assoc] 
lemma set_gain (hp:a⊆ barn o S): armsZ o k S a ⊆ halo k S:= union_subset (halo_subset ..) (biUnion_subset.mpr fun i hi=> Corona.halo_mono le_rfl (singleton_subset_iff.mpr ((inside ..).1 (hp hi))))
variable (s:E→Finset I)(D:E→Support c)(z: E→ℝ)
variable (hs:∀ i:E, (s i).Nonempty)(hq:∀ i:E,s i⊆ barn o (D i))
variable {α δ η β x:ℝ}(hn:0≤ x)
local notation "A'"=> (k+k+1)^4
local notation "Z" i:arg=>Y (D i) (s i)
noncomputable abbrev tiltE (x:ℝ)(i:E):= x^(s i).card*z i
variable (B' :ℕ)(hB:0 < B')(ha:0 ≤ α)(hz:Ac.Hit D B' z α β)(hu:∀ i,0 ≤ z i)
include hs hq hB ha hz hu hn
local notation "ρ"=> x* Real.exp (α*A')
-- transfer leading factor via extended price. no `all-anchors`. note cast A' prefer nat.
local notation "Φ"=> x * Real.exp (α*((k+k+1)^4:ℕ))
lemma drafted (hT:x*Real.exp (α*((k+k+1)^4:ℕ))≤1): Ac.Hit (fun i=>armsZ o k (D i) (s i)) B' (tiltE s z x) α (((k+k+1:ℕ)^4:ℕ)*(Φ*β)):=by
     let f(i: Site c)(j:E):= if i∈D j then z j * Real.exp (α*coverNumber B' (D j)) else (0:ℝ); have hp:∀ i, SumBudget (f i) β:= hz
     have hρ:0 ≤ Φ:=mul_nonneg hn (Real.exp_pos _).le
     intro x'; let H:=halo k {x'}; let t j:= if x'∈ armsZ o k (D j) (s j) then tiltE s z x j * Real.exp (α*coverNumber B' (armsZ o k (D j) (s j))) else (0:ℝ)
     have h:SumBudget (fun j=> Φ*∑ i∈H,f i j) (((k+k+1)^4:ℕ)*(Φ*β)):=by
            refine budget_loosen (budget_scale hρ (budget_over H f (fun _=>β) (fun i _=>hz i))) ?_
            rw[sum_const,nsmul_eq_mul,mul_left_comm]; apply mul_le_mul_of_nonneg_right; exact_mod_cast ((Corona.halo_size {x'} k).trans (by rw[card_singleton,one_mul])); exact mul_nonneg hρ (budget_nonneg (hp x'))
     refine budget_mono h (fun i=>ite_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hn _) (hu _)) (Real.exp_pos _).le) le_rfl) fun j=> ?_
     split; next he=>
           obtain ⟨w,hq',hr⟩:= halo_spec.mp (set_gain o (D j) k (s j) (hq j) he); have hw :w ∈ H:=halo_spec.mpr ⟨x',mem_singleton_self _, (separation_comm x' _).le.trans hr⟩; let hK:=size_gain o (D j) k (s j) (hq j) B' hB
           refine le_trans ?_ (mul_le_mul_of_nonneg_left (single_le_sum (fun i _=> (hp i).1 j) hw) hρ)
           let d:= (s j).card; have hd:0<d:= card_pos.mpr (hs j); let A:= α*((k+k+1)^4:ℕ); let i:= z j; let y:=coverNumber B' (D j)
           let W':= z j*Real.exp (α*y); have hh:f w j=W':=if_pos hq'; let v:= Φ
           apply (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hK) ha)) (show 0 ≤ tiltE s z x j from (mul_nonneg (pow_nonneg hn _) (hu _)))).trans
           calc
           _= v^d*W' := by
                       rw[Nat.cast_add,Nat.cast_mul,mul_add,Real.exp_add]; change x^d*z j*(Real.exp _*Real.exp (α*((d:ℝ)*((k+k+1)^4:ℕ))))= _
                       rw [show α*((d:ℝ)*_)=(d:ℝ)*A from by unfold d A; ring,Real.exp_nat_mul,show v=x*Real.exp A from rfl,mul_pow]; unfold W'; ring
           _≤ v*f w j:=by rw [hh]; apply mul_le_mul_of_nonneg_right _ ((hh ▸ (hp w).1 j)); exact (pow_le_pow_of_le_one hρ hT hd).trans_eq (pow_one _)
     exact h.1 _
end Gain
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Gain.drafted
