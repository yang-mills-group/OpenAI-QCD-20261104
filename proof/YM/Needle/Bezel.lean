import YM.Needle.Shears
/-!
  Convex stencil support tests. Always inside an exact regulator box with frame certificate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) {d:ℕ}(Z:Laurel d) (J:Landing P.sym Z)
local notation "S"=> C.S
set_option quotPrecheck false
local notation "Xι"=>Stokes d→ℂ
local notation "Xµ"=>Fin (deficit d)→ℂ
variable {β ν:ℝ}(hC:C.Path β ν)
variable {P Z J}
namespace GaugeP
variable (K: GaugeP P Z J) (hv:Sway C.S)(G:Capital P d 1) (E:Invest P d)
variable (i:ℕ)
open Investment
-- supports including possible multiplicity
structure Merit (K:GaugeP P Z J)(i:ℕ) where
   n:ℕ
   x:Fin n→ Cover
   w:Fin n→ℝ
   hi :∀ j, K.fault i (x j)
   hw:∀ j,0 ≤ w j
   hs:∑ j,w j=1
namespace Merit
variable {K i}(O: Merit K i)
noncomputable def testR: stalk C i→ₗ[ℂ](Stokes d→ℂ):= ∑ j:Fin O.n, (↑(O.w j):ℂ) • K.heightH i (O.x j)
lemma heldR (f:stalk C i) (v:ℝ)(hf:∀ j:Fin O.n, ‖K.heightH i (O.x j) f‖ ≤ v): ‖O.testR f‖ ≤ v:=by
    unfold testR; rw [LinearMap.sum_apply]; apply (norm_sum_le ..).trans
    simp_rw [LinearMap.smul_apply, norm_smul, Complex.norm_real]; have h(j:Fin O.n): ‖O.w j‖ * ‖K.heightH i (O.x j) f‖ ≤ O.w j*v:=by rw[Real.norm_of_nonneg (O.hw _)]; exact mul_le_mul_of_nonneg_left (hf j) (O.hw _)
    exact (sum_le_sum fun j _=> h j).trans_eq (by rw[← sum_mul,O.hs,one_mul])
noncomputable def solo {x:Cover}(h:K.fault i x): Merit K i:=⟨1,fun _=>x,fun _=>1,fun _=>h,fun _=>zero_le_one,by simp⟩
lemma onlyX {x:Cover}(h:K.fault i x) (y:stalk C i): (solo h).testR y=K.heightH i x y:=by simp [testR,solo] -- test
end Merit
lemma loyalH : ∀ᶠ i in atTop,∀ O:Merit K i,∀ t:Stokes d→ℂ, ‖t‖ ≤ J.J*‖O.testR (stem P d i (K.ridge i t))‖:=by
    filter_upwards [K.shore] with i hi O t
    let W:= stem P d i; let L:= O.testR
    let F(j:Stokes d)(k:Stokes d):=L (W (K.h i k)) j
    let f(j:Fin O.n)(k l:Stokes d):=K.heightH i (O.x j) (W (K.h i l)) k
    have hf(j:Fin O.n): nearG P.sym Z J.ε (f j):=hi (O.x j) (O.hi j)
    have he (j k):F j k= ∑ l:Fin O.n, (↑(O.w l):ℂ)*f l j k:=by unfold F L Merit.testR; rw[LinearMap.sum_apply,Finset.sum_apply]; rfl
    have h:nearG P.sym Z J.ε F:=by
         intro j k; rw [he]; let z:=ΦGram P.sym Z (basis timeAxis) j k
         let V(a:Fin O.n):ℂ:= ↑(O.w a)
         have ht:∑ a:Fin O.n,V a=1:=by unfold V; exact_mod_cast O.hs
         have hu:z=∑ a:Fin O.n,V a * z:=by rw [←sum_mul,ht,one_mul]
         change ‖(∑ a:Fin O.n,V a*f a j k)-z‖ ≤ _
         rw [hu,←sum_sub_distrib]; simp_rw [←mul_sub]; apply (norm_sum_le ..).trans
         have h(a: Fin O.n): ‖V a*(f a j k-z)‖ ≤ O.w a * J.ε:=by unfold V; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (O.hw _)]; exact mul_le_mul_of_nonneg_left (hf a j k) (O.hw _)
         exact (sum_le_sum (fun a _=>h a)).trans_eq (by rw [←sum_mul,O.hs,one_mul])
    apply (J.warmth h t).trans_eq; apply congr_arg; apply congr_arg _ (?_:Γ (d:=d) F t = L (W (K.ridge i t)))
    ext1 j; change (∑ k,F j k*t k) = L (W (∑ k,t k • K.h i k)) j; rw[map_sum,map_sum,Finset.sum_apply]; refine sum_congr rfl fun k _=>?_ ; rw [map_smul,map_smul,Pi.smul_apply]; exact mul_comm ..
include hC G hv
lemma near_race :∃ f:ℕ→ℝ,Tendsto (fun i=>E.scale i*f i) atTop (𝓝 0) ∧∀ᶠ i in atTop,0 ≤ f i∧ ∀ O:Merit K i,∀ t:Fin (deficit d)→ℂ,‖O.testR (stem P d i (Investment.face E i t))‖ ≤ ‖t‖*f i:=by
    obtain ⟨f,h,H⟩:=cheapH hC K hv G E; refine ⟨f,h,H.mono fun i hi=>⟨hi.1,?_⟩⟩; intro O t; apply O.heldR; intro j; exact hi.2 _ (O.hi j) t
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.loyalH
#print axioms YM.Massive.Needle.GaugeP.near_race
