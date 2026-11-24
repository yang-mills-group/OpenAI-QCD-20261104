import YM.Roan.Refl
import YM.Roan.Venue
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.TableT Tawny.Pane Tawny.BendR
open Oriole Counting Counting.Click PCAC Patria.Gall.Seals Patria.Gall
-- incomes cost norm.S
local notation "Z"=> RawVec 10
open Perla Carnal
variable {C:Sequence}{P:Calibration C}{Q: Tarn.Choir} (T:Tarn.Pollens P Q)
variable (i j a:Axis)(v:Flavor 6)(s:RawSym)
set_option quotPrecheck false
local notation "Ω"=> Signed.mirror a
local notation "σ" x:arg => (signT (Signed.mirror a) x:ℂ)
local notation "signs" x:arg y:arg => σ x * σ y
local notation "I"=> (0:Multi 8)
local notation "U" p:arg=> s.adj 8 a p
local notation "V"=> RawTensor 1 8
lemma eph : (U (epi.val (i,j))) = (signs i j) • (epi.val (i,j)):=by
       by_cases h:i=j; · subst j; rw [mirror_sq,one_smul]; apply Subtype.ext; rw [s.adjActs,epi_at,if_pos rfl]; change adj a _=_; unfold adj UV.unit; rw [TensorProduct.map_tmul,LinearMap.comp_apply,LinearMap.comp_apply, show conjGPol 1=1 from map_one (MvPolynomial.map (starRingEnd ℂ)), dagger_one, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_one,map_one]
       have hV: epi.val (i,j) =0:=by apply Subtype.ext; rw [epi_at,if_neg h]; rfl
       rw [hV,map_zero,smul_zero]
noncomputable def slotB : Fin 4 →RawTensor 1 8:= ![epi,spire,shadow,eclipse]
lemma meanB (d:Fin 4):(U ((slotB d).val (i,j)))=signs i j • ((slotB d).val (i,j)):=by
       have h(i j:Axis):s.adj 8 a (spire.val (i,j)) = (signs i j) • (spire.val (i,j)):=by
             rw [spire_val, map_sum, smul_sum]; apply sum_congr rfl; intro k _; rw[GGov]; congr 1
             calc σ i* σ k* (σ j* σ k)=(σ i*σ j)*(σ k*σ k):=by ring
                  _ = _:=by rw[mirror_sq,mul_one]
       have he(i j:Axis):s.adj 8 a (shadow.val (i,j))=signs i j • shadow.val (i,j):=by rw [show shadow.val (i,j)= if i=j then spire.val (i,j) else 0 from rfl]; split; exact h i j; rw[map_zero,smul_zero]
       have hp(i j:Axis): s.adj 8 a (eclipse.val (i,j))=signs i j • eclipse.val (i,j):=by
             rw [dark]; split; next h=>subst j; rw[mirror_sq,one_smul,map_sum]; apply sum_congr rfl; intro k _; rw[map_sum]; apply sum_congr rfl; intro t _; rw [GGov,show (signs k t)*(signs k t)= (σ k*σ k)*(σ t*σ t) from (by ring),mirror_sq,mirror_sq,mul_one,one_smul]
             rw [map_zero,smul_zero]
       fin_cases d; exact eph ..; exact h ..; exact he ..; exact hp ..
local notation "XX"=> poseσ
lemma spinTurn (x:Values 4)(v:Fin 4→ℂ) : s.adj 8 a ((poseσ (x,v)).val (i,j))=(signs i j) • ((poseσ (star x,star v)).val (i,j)):=by
       have hh(x:Values 4)(v:Fin 4→ℂ):poseσ (x,v)=(∑ i:Flavor 6, ∑ j:Fin 4, x i j • slotsS i j)+ ∑ j:Fin 4,v j • slotB j:=by
              change (∑ i:Flavor 6,axisσ i (x i))+gaugeσ v= _; simp_rw[Fin.sum_univ_four]; rfl
       rw [hh,hh]; simp only[Submodule.coe_add,AddSubmonoidClass.coe_finsetSum, Pi.add_apply,Finset.sum_apply,map_add,map_sum,Submodule.coe_smul,Pi.smul_apply,map_smulₛₗ,loyal_cell, meanB,starRingEnd_apply,Pi.star_apply]
       rw [smul_add]; congr 1
       · rw [smul_sum]; refine sum_congr rfl fun i _=>?_ ; rw[smul_sum]; exact sum_congr rfl fun j _=>smul_comm ..
       rw [smul_sum]; exact sum_congr rfl fun j _=>smul_comm ..
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.spinTurn
