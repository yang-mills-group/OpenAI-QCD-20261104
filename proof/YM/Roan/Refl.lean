import YM.Avian.Wards
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
lemma mirror_sq(x:Axis):σ x*σ x=1:=by rw [←Complex.ofReal_mul,sign_sq,Complex.ofReal_one]
lemma gamma_echo : gamma a * gamma i * gamma a= -(σ i) • gamma i:= by
        by_cases h:i=a
        · subst i; simp [signT,Signed.mirror]
        rw[Lat.clifford (Ne.symm h),neg_mul,mul_assoc,Lat.gamma_sq,mul_one]; simp [signT,Signed.mirror,Ne.symm h]
lemma alter_p : s.adj 8 a (alter v i j)=(σ i * σ j) • (alter v i j):=by
     apply Subtype.ext; rw [s.adjActs,Submodule.coe_smul,Carnal.amt]; unfold UV.spinStressUnsymm; rw[map_sub, youth,youth]; rw[gamma_star,gamma_echo]; simp_rw [marked_root,vital,mul_one,one_mul]; rw[nourish,nourish]; rw[smul_sub]; simp_rw [smul_smul]; rw [show (σ j)*(-(σ i))= -(σ i * σ j) from by ring]; simp_rw [neg_smul]; abel
lemma GGov(p q:Axis): s.adj 8 a (GG i j p q)=(signs i j*(signs p q)) • GG i j p q:=by
     obtain ⟨w,hw⟩:= EuPin.choice Ω; have ht := payG i j p q Ω w hw
     have hE:pinAct w (GG i j p q).val=(signs i j*(signs p q)) • (GG i j p q).val:=ht
     let X: GPol:= (StressFlux.pair su i j p q).val; have he:conjGPol X=X:=by apply Labels.eval_ext; intro J; rw[conj_values]; unfold X; rw[StressFlux.pair_value]; exact Complex.conj_ofReal _
     apply Subtype.ext; rw[s.adjActs,Submodule.coe_smul,←hE, show (GG i j p q).val=plain 8 X from rfl,plainT _ Ω w hw,plainP ,plainP,adj,TensorProduct.map_tmul]; simp [he, Grass.dagger_one]; rfl -- check
-- inherit components, f.S basis Tau table. orbit.L.v pose. def
open Carnal
local notation "mS"=> scalarS
lemma dusk (L:Label 8)(he:L.val=UV.bilinear v v 1 0 0): (U L)= L:=by apply Subtype.ext; rw [s.adjActs,he,youth,star_one,mul_one, Lat.gamma_sq,marked_root,mul_one,Complex.ofReal_one,one_smul]
noncomputable def slotsS (v:Flavor 6): Fin 4→ RawTensor 1 8:= ![scalarS v,sunS v,wingS v,traceT v]
lemma loyal_cell (d:Fin 4): s.adj 8 a ((slotsS v d).val (i,j))=(σ i* σ j) • ((slotsS v d).val (i,j)):=by -- lookup
     have he(i j:Axis): s.adj _ a ((sunS v).val (i,j))=(signs i j) • (sunS v).val (i,j):=by rw[W_sun,map_add, alter_p,alter_p,mul_comm (σ j),smul_add]
     have hM(i j:Axis): s.adj _ a ((scalarS v).val (i,j))= signs i j • ((scalarS v).val (i,j)):=by
           rw[W_mass]; by_cases h:i=j; subst j; rw[if_pos rfl,mirror_sq,one_smul]; exact dusk a v s _ rfl
           rw[if_neg h,map_zero,smul_zero]
     have hW(i j:Axis):s.adj _ a ((wingS v).val (i,j))= signs i j • ((wingS v).val (i,j)):=by rw [W_wing]; split; exact he i j; rw [map_zero,smul_zero]
     have hτ(i j:Axis):s.adj _ a ((traceT v).val (i,j))= signs i j • ((traceT v).val (i,j)):=by
           rw [W_trace]; split; next h=> subst j; rw [mirror_sq,map_sum,one_smul]; simp_rw [alter_p,mirror_sq,one_smul]
           next h=> simp
     have h:i=i:=rfl -- branch above adjust
     fin_cases d; exact hM ..; exact he ..; exact hW ..; exact hτ ..

end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.loyal_cell
