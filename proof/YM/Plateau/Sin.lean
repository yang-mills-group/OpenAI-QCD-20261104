import YM.Plateau.Tea
import YM.Plateau.Firth
/- The charged sector polynomial recovered by all funding operations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open Poised Plans Plans.Stamp Poised.Stative
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)
variable (p q:Flavor 6)(g t:Bool)
open Massive.Oriole
variable (α β γ χ ξ σ ρ z:ℝ)(F:ℕ→ Set (Label 8))
local notation "X"=> Style p q g
local notation "P★"=> Q.focus MassFields.isotropic 8
local notation "vL"=> parL t g
local notation "vR"=> parR t g
variable (hp:p≠q)(hH: Q.Harmony P φ)(hφ:Tendsto φ atTop atTop)
variable (hP:∀ (q:ℕ→ Label 8)(w:ℕ→ℕ)(ht:StrictMono w), (∀ᶠ i in atTop,q i∈ F i) →∀ x, Tendsto (q ∘ φ ∘ w) atTop (𝓝 x)→∃ z:Label 8,Q.focus MassFields.isotropic 8 z=0∧‖x-z‖ ≤ χ)
variable (hR:∀ᶠ i:ℕ in atTop,∃ x y v:ℂ, ‖x+z‖ ≤ α ∧ ‖y-parL t g‖+‖v-parR t g‖ ≤ β ∧ Style p q g x y v∈ F i)
variable (μ δ:ℝ){J:Label 8→ₗ[ℂ] Label 8}(h8:Ami 8 p q g true J)(hμ:∀ x y z:ℂ,‖x‖+‖y‖+‖z‖≤ μ*‖Style p q g x y z‖)
include T hp hH hP hφ hR h8 hμ
lemma sinks (hpμ:0<μ)(hα:0≤ α)(hβ:0 ≤ β)(h: μ*(‖J.toContinuousLinearMap‖*χ)≤δ) : ∃ x y v:ℂ, Q.focus MassFields.isotropic 8 (Style p q g x y v)=0 ∧ ‖x+z‖≤ α+δ∧ ‖y-vL‖+‖v-vR‖≤β+δ:=by
       obtain ⟨N,hN⟩:= eventually_atTop.mp hR; choose! c s f h1 h2 h3 using hN; let t':=t; let G(i:ℕ): Label 8:= Style p q g (c i) (s i) (f i)
       let M:= α+‖(z:ℂ)‖+(β+‖vL‖)+(β+‖vR‖); let X'(j:Fin 3)(i:ℕ):= (![c (φ i),s (φ i),f (φ i)]:Fin 3→ℂ) j
       have hm:0 ≤ M:=by unfold M; positivity
       obtain ⟨w,hw,f',H⟩:= YM.Fir.Lantern.armor X' (fun i=>⟨M,hm,(hφ.eventually_ge_atTop N).mono fun j hj=> by
               let n:=φ j; have hL:‖s n‖≤ β+‖vL‖:=sub_le_iff_le_add.mp ((norm_sub_norm_le ..).trans (by linarith only [show _+‖f n-vR‖≤β from h2 n hj,norm_nonneg (f n-vR)])) -- signature
               have hK: ‖f n‖ ≤ β+‖vR‖:=by linarith only [norm_sub_norm_le (f n) vR,h2 n hj,norm_nonneg (s n-vL)]
               have hP : ‖c n‖ ≤ α+‖(z:ℂ)‖:=by have he:= (norm_sub_le (c n+z) (z:ℂ)).trans (add_le_add_left (h1 n hj) _); rwa [add_sub_cancel_right] at he
               fin_cases i
               · change ‖c n‖≤ M; unfold M; linarith only [hP,hβ,norm_nonneg vL,norm_nonneg vR]
               · change ‖s n‖≤ M; unfold M; linarith only [hL,hα,hβ,norm_nonneg (z:ℂ),norm_nonneg vR]
               change ‖f n‖≤ M; unfold M; linarith only [hK,hα,hβ,norm_nonneg (z:ℂ),norm_nonneg vL]⟩)
       let τ:=φ∘w; let x:= f' 0; let y:= f' 1; let P':= f' 2; have H1:Tendsto (fun i=> c (τ i)) atTop (𝓝 x):= H 0; have H2:Tendsto (fun i=>s (τ i)) atTop (𝓝 y):=H 1; have H3:Tendsto (fun i=>f (τ i)) atTop (𝓝 P'):= H 2
       have hδ:= (hφ.comp hw.tendsto_atTop).eventually_ge_atTop N; have hx: ‖x+z‖ ≤ α:=le_of_tendsto (H1.add_const (z:ℂ)).norm (hδ.mono fun i hi=> h1 (τ i) hi); have hy: ‖y-vL‖+‖P'-vR‖≤β:=le_of_tendsto ((H2.sub_const _).norm.add (H3.sub_const _).norm) (hδ.mono fun i hi=> h2 (τ i) hi)
       let V: Label 8:= Style p q g x y P'; obtain ⟨zQ,hz,hK⟩:= hP G w hw (eventually_atTop.mpr ⟨N,h3⟩) V (((H1.smul_const (flame p q g 8 (by decide))).add (H2.smul_const (arbor p q g true))).add (H3.smul_const (arbor p q g false)))
       obtain ⟨x',y',q',hp,hL'⟩:= arms T p q g h8 hp μ hμ hpμ x y P' zQ hz χ δ hK h
       refine ⟨x',y',q',hp,?_,?_⟩; · rw [show x'+z=(x+z)-(x-x') from by ring]; linarith only [norm_sub_le (x+(z:ℂ)) (x-x'),hx,hL',norm_nonneg (y-y'),norm_nonneg (P'-q')]
       linarith only [norm_sub_le_norm_sub_add_norm_sub y' y vL, norm_sub_le_norm_sub_add_norm_sub q' P' vR, hL',hx,hy,norm_nonneg (x-x'),norm_sub_rev y y',norm_sub_rev P' q']
end YM.Sprig
#print axioms YM.Sprig.sinks
