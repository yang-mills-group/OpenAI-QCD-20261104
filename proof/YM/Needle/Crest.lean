import YM.Needle.Vista
/-!
  Rank probe prices sustained from all interior placements in the physical volume.
  Allow arbitrary ERA-specific averages without determining persistence a priori.
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
local notation "Vᴮ" i:arg => (C.A i).regulator
local notation "Ω"=>Intag.Vale.Stokes d
local notation "a" i:arg=> C.S.spacing (C.N i)
variable {β ν:ℝ}(hC:C.Path β ν)
variable {P Z J}
namespace GaugeP
variable (K: GaugeP P Z J) (hv:Sway C.S)(G:Capital P d 1)
variable (i:ℕ)
noncomputable def heightH (x:Cover): stalk C i →ₗ[ℂ] (Stokes d→ℂ):=LinearMap.pi (fun j:Stokes d=> duet C i (K.heads i j) 0 x)
open Investment
lemma vision : ∀ᶠ i in atTop,∀ x:Cover, K.fault i x→ ∀ t: Stokes d → ℂ, ‖t‖ ≤ J.J * ‖K.heightH i x (stem P d i (K.ridge i t))‖:=by
    filter_upwards [K.shore] with i hi x hx t
    let V:= K.heightH i x; let f(j l:Stokes d):=duet C i (K.heads i j) 0 x (stem P d i (K.h i l));
    have he:K.heightH i x (stem P d i (K.ridge i t)) = Γ (d:=d) f t:=by
        ext1 j; let T:= duet C i (K.heads i j) 0 x
        change T (stem P d i (∑ k,t k • K.h i k))=∑ k,f j k*t k; rw [map_sum, map_sum]; refine sum_congr rfl fun k _=>?_; rw [map_smul,map_smul]; exact mul_comm ..
    rw[he]; exact J.warmth (hi x hx) t
include hC G hv
lemma valves: ∀ᶠ j in atTop,∃ L:ℝ,0 ≤ L∧ ∀ᶠ i:ℕ in atTop,∀ x:Cover, K.fault i x → ∀ U:stalk C i,∀ z:ℝ,0 ≤ z → GreenP C i j U z→ ‖K.heightH i x U‖ ≤ L * z:=by
    obtain ⟨e,he,h⟩:= sepF hC K
    obtain ⟨N,hN,hP⟩:= shyness hC e he 0
    filter_upwards [hv.high.eventually (eventually_gt_atTop (6*2)),(G.gains (v:=K.price)),eventually_ge_atTop N] with j hj hJ ht
    let V:= K.price*Hub.rayM C.S d 1 G.v j; have hV:0≤V:=mul_nonneg K.realH (G.power _)
    refine ⟨V,hV,?_⟩; filter_upwards [h,hJ,hC.uv.tendsto_atTop.eventually_ge_atTop (j+1),K.tall] with i hi hs hl hp x hx U z hz hu
    have h': seaM C i j (![0,x]:Fin 2→ Cover):= tide j i _ (hi x hx) (le_trans (Nat.le_succ _) hl) (lt_of_le_of_lt (spacing_antitone C.S ht) hP)
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hV hz)).2 fun k=>?_
    have hc:= hs (K.g i k) (hp k).1; let f: Fin 2→ stalk C i:=![K.heads i k,U]; let v:Fin 2→ℝ:= ![V,z]; have hy(s:Fin 2): GreenP C i j (f s) (v s):=by fin_cases s; exact hc; exact hu
    have hh:= reapS i j f v hC hy ![0,x] h' hj hl
    unfold readS at hh; simp only[List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil, mul_one,f,v,Fin.prod_univ_succ] at hh; change ‖((C.A i).regulator).average ((K.heads i k) 0* U x)‖ ≤_; simpa using hh
variable (E:Invest P d)
lemma cheapH : ∃ f:ℕ→ℝ,Tendsto (fun i=>E.scale i*f i) atTop (𝓝 0) ∧ ∀ᶠ i in atTop,0 ≤ f i∧ ∀ x:Cover, K.fault i x → ∀ t:Fin (deficit d)→ ℂ, ‖K.heightH i x (stem P d i (Investment.face E i t))‖ ≤ ‖t‖ * f i:=by
    obtain ⟨j,⟨L,hv,H⟩,f,hf,hP⟩:= ((valves hC K hv G).and (creditW E)).exists; refine ⟨fun i=> f i*L,?_,?_⟩
    · simpa only [zero_mul,mul_assoc] using hf.mul_const L
    filter_upwards [H,hP] with i hi hu; refine ⟨mul_nonneg hu.1 hv,fun x hx t=>?_⟩; exact (hi x hx _ _ (mul_nonneg (norm_nonneg _) hu.1) (hu.2 t)).trans_eq (by ring)
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.vision
#print axioms YM.Massive.Needle.GaugeP.cheapH
