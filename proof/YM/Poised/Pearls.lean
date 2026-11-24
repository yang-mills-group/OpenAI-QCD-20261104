import YM.Poised.Ivory
import YM.Poised.Somni
/-! # Exact off-shell.L ruling, through all roots admissible -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Chute
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource Cruising MultiNext.SignedSource.Lyre
variable {K: KernelChoices}(P:Flight j k)(h:l.val=c.val*P.L.val)(T:Tube su (Flight.visit P K h))
variable {X:Support l}{Y:Support c}{b b':Cover} {u v L:ℕ} {τ t vo A C a :ℝ}
open Display Kites
abbrev recital (d:ℕ)(J:Labels.Jet su)(l:Side)(b:Cover)(H:TaperHol)(v:ℝ)(s:ℝ):Pipes.Path l (ZBand d):=(lode d J l b H s,woe H.T b v s d)
lemma recital_jet (l:Side)(b:Cover)(H:TaperHol)(J:Labels.Jet su)(vo:ℝ)(hn:n≤d): iteratedDeriv n (recital d J l b H vo) 0= echoG l b H J vo d n:=by
    have hh : ContDiffAt ℝ n (recital d J l b H vo) 0:= ((lode_smooth J d H l b).prodMk (woe_smooth H.T b vo d)).of_le (Nat.cast_le.mpr hn)
    apply Prod.ext; · exact (Display.clm_step (recital d J l b H vo) n 0 hh (ContinuousLinearMap.fst ℝ _ _)).symm
    exact (Display.clm_step (recital d J l b H vo) n 0 hh (ContinuousLinearMap.snd ℝ _ _)).symm
lemma stays (J: Labels.Jet su)(d:ℕ)(U:Grid l)(H:TaperHol)(b:Cover): current H b d J =ᶠ[𝓝 0] increment (1:Grid l) ∘ lode d J l b H:=by
    let q:=scaledD d J; have h:Tendsto q (𝓝 0) (𝓝 0):=by have hh:= (scaled_smooth d J).continuousAt.tendsto; rwa [scaled_zero] at hh
    exact h.eventually (at_east H b)
lemma pscale (v:ℝ)(U:Lat.Fields l 6)(t:ℝ)(H:TaperHol)(b:Cover): changeVars (woe H.T b v t d) U = engine v (ZBand d) (changeVars (chain H.T b t d) U):=by
   letI : DecidableEq (ZBand d):=Classical.decEq _; unfold engine; rw [← AlgHom.comp_apply,←change_mul]; apply congr_arg (fun q:Matrix (Faces (Site l)) (ZBand d) ℂ=> changeVars q U); ext i j; rw [Matrix.mul_diagonal]; change v • (chain H.T b t d i j) = (chain H.T b t d i j)*_; rw [Complex.real_smul,mul_comm]
lemma dressedT (F:Grid l→ Lat.Fields l 6)(H:TaperHol)(J:Labels.Jet su)(b:Cover)(v:ℝ)(d:ℕ):
     engine v (ZBand d) ∘ moment H b J F =ᶠ[𝓝 0] (lotsF F ∘ recital d J l b H v):=by
    filter_upwards [stays J d (1:Grid l) H b] with s hs; change _=changeVars (woe H.T b v s d) (F (increment _ (lode d J l b H s))); rw [pscale]; apply congr_arg (engine v (ZBand d)); rw [Beacon.moment,hs]; rfl
variable (H:TaperHol)(J:Labels.Jet su) (F:Grid l→Lat.Fields l 6)(he:Rooted X F)(hf:ContDiffAt ℝ d (F∘increment 1) 0) (hF:∀ k U,slots 6 k (F (Lattice.gauge k U))=F U)
variable (hΩ:Nonwrapping X (wrap l b))(hS:100≤l.val)(hT: T.R.A0=linesOf P a)(ha:0<a)(hk:4≤k)(hn:n≤d)
variable (h0:∀ (J:Labels.Jet su)(k:ℕ), k<n→ WardBin.leading k (Beacon.moment (d:=d) H b J F)=0) (hΔ:d/2 ≤ j)
include hn he hf
local notation "JT"=> t • J
local notation "f0"=> fun (i:ℕ)=> craftT d i (b:=b) (X:=X) (b':=b') P h T J vo t
local notation "J'"=> fun i:ℕ=> mintT X b H JT vo d i
local notation "s₀"=>Kit.slope P.L
lemma source : iteratedDeriv n (engine vo (ZBand d) ∘ Beacon.moment H b JT F) 0= ∑ i : OrderedFinpartition n, iteratedFDeriv ℝ i.length (lotsF F) 0 (fun j => J' (i.partSize j)):=by
   rw [(dressedT F H JT b vo d).iteratedDeriv_eq]; let v:=recital d JT l b H vo; have hV:v 0=0:=Prod.ext (inPlace JT d H l b) (woe_nil (c:=l) H.T b vo d)
   rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition (show ContDiffAt ℝ (d:WithTop ℕ∞) _ (v 0) from hV.symm ▸ lots_alive F hf) (show ContDiffAt ℝ (d:WithTop ℕ∞) v 0 from (lode_smooth JT d H l b).prodMk (woe_smooth H.T b vo d)) (Nat.cast_le.mpr hn),hV]
   refine sum_congr rfl fun i _=> (melody X F he _ _ (fun j=>?_) (hf.of_le (Nat.cast_le.mpr (i.length_le.trans hn)))).symm; unfold v; rw [recital_jet l b H JT vo ((i.partSize_le j).trans hn)]; exact real_at H JT
omit hn he hf
lemma buoy_w [Fintype B](q:ℝ){Y:Pipes.Path l B}(h: Buoyant Y X b n): Buoyant (q • Y) X b n:=by
   obtain ⟨⟨p,hp,g⟩,Z,hZ,H⟩:=h
   refine ⟨⟨q • p,Submodule.smul_mem _ _ hp,fun i hi=>?_⟩,q • Z,Submodule.smul_mem _ _ hZ,fun i hi=>?_⟩
   · change q • (Y.1 i)= _; rw [g i hi]; rfl
   change q • asks Y.2 i= _; rw [H i hi,smul_comm q]; rfl
include hn he hf
include hΩ hS hT ha hk hΔ hF h0
lemma trueT (i:OrderedFinpartition n): iteratedFDeriv ℝ i.length (lotsF F) 0 (fun j=> f0 (i.partSize j)) = (Kit.slope P.L)^n • iteratedFDeriv ℝ i.length (lotsF F) 0 (fun j=>J' (i.partSize j)):=by
   let f(j):=f0 (i.partSize j); let g(j):=s₀^(i.partSize j) • (J' (i.partSize j)); let A:=iteratedFDeriv ℝ i.length (lotsF (B:=ZBand d) F) 0
   have heV: (∑ j:Fin i.length, i.partSize j)=n:=by simpa using i.sum_sigma_eq_sum (fun _=>(1:ℕ))
   rw [show iteratedFDeriv ℝ i.length (lotsF F) 0 (fun j=>f0 _) = ∑ j:Finset (Fin i.length),A (j.piecewise (f-g) g) from by rw [← A.map_add_univ,sub_add_cancel]]
   have hz:= hf.of_le (show (i.length:WithTop ℕ∞) ≤ d from Nat.cast_le.mpr (i.length_le.trans hn))
   have hv(j):Buoyant (f j-g j) X b (i.partSize j-1):= heightsT P h T H J hΩ hS hT ha hk ((i.partSize_le j).trans hn) hΔ
   have ht(j): Buoyant (g j) X b (i.partSize j):= buoy_w (s₀^_) (telling H J hΩ hS ((i.partSize_le j).trans hn))
   rw [sum_eq_single ∅]
   · rw [Finset.piecewise_empty,A.map_smul_univ] -- fails g not unfolded
     rw [prod_pow_eq_pow_sum,heV]
   · intro j _ hj; let p(k:Fin i.length):=if k∈j then i.partSize k-1 else i.partSize k; let X₀:= j.piecewise (f-g) g; have hp(k): Buoyant (X₀ k) X b (p k):= by
        by_cases hs : k∈j
        · unfold X₀; rw [Finset.piecewise_eq_of_mem _ _ _ hs]; unfold p; rw [if_pos hs]; exact hv k
        unfold X₀; rw [Finset.piecewise_eq_of_notMem _ _ _ hs]; unfold p; rw [if_neg hs]; exact ht k
     by_cases h:∀ k, 2 ≤ p k
     · obtain ⟨s,hs⟩:= Finset.nonempty_iff_ne_empty.mpr hj; refine cancels b H X hΩ hS F he hF hf n (by omega) h0 X₀ p h ?_ hp; apply lt_of_lt_of_le (Finset.sum_lt_sum (g:=i.partSize) (fun a _=>by unfold p; split <;> omega) ⟨s, Finset.mem_univ _,?_⟩) heV.le; unfold p; rw [if_pos hs]; have he:=i.partSize_pos s; omega
     push Not at h; obtain ⟨k,h⟩:=h; exact buoy_zero he X₀ k (buoy_sized (hp k) (by omega)) hz
   simp
lemma pricerT : (∑ i : OrderedFinpartition n, iteratedFDeriv ℝ i.length (lotsF F) 0 (fun j=> f0 (i.partSize j))) = (Kit.slope P.L)^n • iteratedDeriv n (engine vo (ZBand d) ∘ Beacon.moment H b JT F) 0:=by
   rw [source H J F he hf hn, Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _=> trueT P h T H J F he hf hF hΩ hS hT ha hk hn h0 hΔ i)
end Chute
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Chute.pricerT
