import YM.QCD.Octave.Cast
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Octave
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam Cove Golden NormedSpace
open scoped Topology ENNReal ContDiff BigOperators Classical
open Lat YM.Next.Free Reggae
open Jets.Touch Port Kit Run Stew Bay Strut Leaf Tee Flume Garden Kings Orbit LeafM
open scoped Matrix.Norms.L2Operator
open Revolve
open Loom Fleet
open AtomF
open Loom Fleet AtomF Oasis
variable {N:ℕ}{s:ℝ}{σ c f:Side}{K : KernelChoices}{V Z R A v u a b t t' C D E m δ p α H:ℝ}{q k j i l n:ℕ}
variable {S:StepData c f}(F:Forest S.ratio) (G:Flight j k)(w:f.val=c.val*G.L.val) (P:Plan j)(J:Offer 1 u C)(T:Offer 2 a D)(W:ℕ→Atom su 2)
local notation "X"=>park G w P J T p m
local notation "Y"=>park G w P J T δ m
lemma hyphen (hu:0<u)(ha:0<a)(ht:0<t)(ht':0<t')(hx:Species G w V R t b H n X)(hy:Species G w V R t' b H n Y)(hq:0<p)(hp:p≤1)(he:0<δ)(hr:δ≤1)(hB: Own f t b i (probe V X W) A): let P:= projection (G:=su) F
    Eyrie.Duet (tonic w X W N s∘P) (tonic w Y W N s∘P):=by
   intro P'; obtain ⟨y,hY,hQ,hκ⟩:=chartG F
   have hv:= duct y (truce W J T hu ha ht hx hq hp hy ht' he hr hB (N:=N) (s:=s)) hQ hY
   have hm (f:Grid f→EvenA c N) : (f∘ Stationary.input su _ ) ∘ y=ᶠ[𝓝 0] (f∘P'):= hκ.mono fun i hi=> congr_arg _ hi.symm
   exact ((Eyrie.Duet.together hv.leftF (hm _)).flip.chain hv).chain (Eyrie.Duet.together hv.rightF (hm _))
variable {N₁ K₁:ℕ} {ξ:ℝ}
lemma revenueT (hp:0<p)(ht:0<b) (P:Plan j) (A R Z C t:ℝ)(N:ℕ)(L:Side)(hv :0<t):∃ ν V Yq D B s:ℝ,∃ i n :ℕ,0<ν∧ 0<s∧s≤1∧ 0≤ B ∧ ∀ (J:Offer 1 p R)(T:Offer 2 b C)(W:ℕ→Atom su 2), Extra.Iteration.Charged W t Z → Extra.Iteration.SymmetricAtoms W → ∀ (c f:Side)(G:Flight j k)(e:f.val=c.val*G.L.val)(m a:ℝ), G.L=L → 0<a→ a≤ s→ |m|≤ s → let Xq:=park G e P J T a m; Species G e V Yq (ν*a^2) 0 D i Xq ∧ Own f (ν*a^2) 0 n (probe V Xq W) B := by
    obtain ⟨η,u,R',r,T,hT,h',hη,i,hi⟩:= ceremony hp ht (show 0≤(0:ℝ) from le_rfl) P k L C R -- verify params
    obtain ⟨B,D,hB,hD,n,h⟩:=robe_price hv Z A (show 0 ≤ (0:ℝ) from le_rfl) 2
    let ξ:= T/(max 1 (η/D+1)); have hξ:0<ξ:=div_pos hT (zero_lt_one.trans_le (le_max_left ..)); have hh: ξ ≤ T:=div_le_self hT.le (le_max_left ..)
    refine ⟨η,u,R',r,|R'|+B,ξ,i,max i n,hη,hξ,hh.trans h',(by positivity),fun J T' W hw ht' c f G e m a hg ha hp' hu=> ?_⟩; intro Xq
    have hx:= hi i le_rfl J T' G c f e a m hg ha (hp'.trans hh) (hu.trans hh)
    have hz:η*a^2≤ D:=by
       have ht:a ≤D/η:=by
          apply hp'.trans; unfold ξ; apply le_trans (div_le_div_of_nonneg_right h' (zero_le_one.trans (le_max_left ..))); rw [div_le_div_iff₀ (zero_lt_one.trans_le (le_max_left ..)) hη]; nlinarith only [hD, mul_le_mul_of_nonneg_left (le_max_right 1 (η/D+1)) hD.le,show D*(η/D)=η by field_simp]
       have hv:a^2≤ a:=by rw [pow_two]; exact mul_le_of_le_one_right ha.le (hp'.trans (hh.trans h'))
       nlinarith only [mul_le_mul_of_nonneg_left hv hη.le,(le_div_iff₀ hη).mp ht]
    refine ⟨hx, (((pieties hx.clump (le_max_left ..) le_rfl).sub ((h f (max i n) (le_max_right ..) W hw ht').clip hz)).mono (add_le_add (le_abs_self _) le_rfl))⟩
end YM.QCD.Octave
