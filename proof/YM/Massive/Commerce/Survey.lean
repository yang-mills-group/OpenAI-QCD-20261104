import YM.QCD.King.Stone
/-!
# Removing the full-flavor hypothesis from the raw integrations

It will be necessary to use expansions on complex-parameter families,
keeping only the gauge symmetry (and in some applications rotations
and diagonal flavor). Even the analytic/differential estimates in
`Loom.chartered` require `Pant`, which both requires real and also all
flavor symmetries! With such a hypothesis those might not be available
off the λ=0 point. Here are versions with the reduced requirements.
Only `hv.warp` not the other Peace data were used in the survey and gold
estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.King
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Golden
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open Push.AbsoluteSums Mixed Trees Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (Ξ : Utopia H j v η r C' χ)
set_option quotPrecheck false
open Pipe
variable {w':ι→ℝ}{Ω Λ t u pu θ e:ℝ}
variable (K':Kite Ξ A b Ω n pu k θ) (hw:Guest Y r A Λ t w' e v η χ j) (hp:Y.Famous)(hx:Y.speaking)
include K' hw hp hx
open Ursell Gas QCD.GasP
lemma survey_frame (p:Clusters Y.Bright)(w:ℝ) (hU:Mode V x j v)(he:Healthy (Pressure.temp s) (seatP Y.lightF p) (V x))(hr: ∀ i,Zest (fun u v=> Y.works i u (V v)) x j)(A':Clusters Y.Bright→RegularAddress c)(hv:(∀ z, Y.sings z (QCD.Sway.OrbitG.trade (Lat.rotates N z)).passL)) :
 let y:= (crude Y χ A').view p ∘ V; let Q x':=stewP Y j (2*j+k) (lushR j Ω r Λ pu) (checkL Ξ w' t w) (Subtype.val (x':Y.Bright));
 ContDiffAt ℝ (↑j :WithTop ℕ∞) y x∧ Brush j (badgeD Y j p Q) 1 (songT e∘y) x:=by
   intro y q'; let f i u:=Y.brisk (p.2 i).val χ (V u); have hx' i : Healthy (Pressure.temp s) (Y.lightF (p.2 i)) (V x):= Finset.disjoint_of_subset_left (subset_biUnion_of_mem (Y.lightF ∘ p.2) (mem_univ i)) he
   have he i:= enrolled Y Ξ K' hw hp hx (p.2 i) w hU (hx' i) hr
   have hf: y=ᶠ[𝓝 x] fun i=> Y.furnace χ (V i) p:=by
      have hz l:= navP Y Ξ K' hw hp hx (p.2 l) (p.2 l) hU (hx' l)
      filter_upwards [eventually_all.mpr hz] with i hi
      let g (y:Site c→su.El):= sways (Lat.rotates N y)
      have hQ z : g z (Y.furnace χ (gauge z (V i)) p)=Y.furnace χ (V i) p:=by
         unfold furnace termP; rw [eSM (g z) (hv z).cont,eSM (g z) (hv z).cont,map_prod]; apply congr_arg; apply congr_arg; exact prod_congr rfl (fun i _=> hi i z (g z) (hv z) (surfeit (Lat.rotates_law ..)))
      change (∫ z,g z (Y.furnace _ _ p) ∂brine c)=_; simp_rw [hQ]; simp
   refine ⟨(ContDiffAt.const_smul _ (ContDiffAt.const_smul _ (contDiffAt_prod (t:= Finset.univ) (fun i _=>(he i).1)))).congr_of_eventuallyEq hf,?_⟩ -- annotation
   let t₁:=coefficient (blocked Y.lightF) p.2; let m:ℝ:=(p.1+1).factorial; let L:=wearK c N e
   have hv := (((rosesC univ (fun i=>L ∘ f i) (fun i=>q' (p.2 i)) (fun i _=> (he i).2))).smul t₁).smul m⁻¹
   rw [show ‖m⁻¹‖*_= badgeD Y j p q' from ?_] at hv
   · apply hv.shimmy; filter_upwards [hf] with i hi; change L _= _; rw [show y i=_ from hi]; change songT e (m⁻¹ • (_ • _))= _; rw [map_smul,map_smul]; rw [show songT e (∏ j,f j i)=_ from map_prod L ..]; rfl
   · unfold badgeD clusters; rw [norm_inv,Real.norm_of_nonneg (by unfold m; positivity : 0 ≤ m)]; rw [div_eq_inv_mul,Real.norm_eq_abs]
end YM.ConnectedActivityE6.Blaze.King
namespace YM.ConnectedActivityE6.Blaze.King
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Golden
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open Push.AbsoluteSums Mixed Trees Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (Ξ : Utopia H j v η r C' χ)
set_option quotPrecheck false
open Pipe
open March Territory QCD.GasP Gas Ursell QCD.Stew
variable {w:ℕ}{w':ι → ℝ}{Ω Λ t u pu θ e δ r':ℝ}
variable {C_:RegularAddress c}{U₀:Config su c}{p:BudgetPoint}{Z':Config su c → EvenA c N}
variable (K':Kite Ξ A b Ω n pu k θ) (hw:Guest Y r A t u w' e v η χ j) (hp:Y.Famous)(hx:Y.speaking)
variable (Z:Clusters Y.Bright → RegularAddress c)
include K' hw hp hx
lemma gold_frame (hg:Territory.Gate Y)(hA:∀ i,(Z i).support=seatP Y.lightF i)(i:Clusters Y.Bright)(hQ:p.order=j)(he:0<v)(ha:0<e)(hk: Sailor su p.threshold Λ j)(hM:p.threshold=Pressure.temp s)(hz:0≤ Λ)(hv:j*Λ ≤ v) (w:ℝ)(hn:(∀ z, Y.sings z (QCD.Sway.OrbitG.trade (Lat.rotates N z)).passL))
 (hP:∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](V:E → Config su c)(x:E), Mode V x j v → ∀ i,Zest (fun u y=> Y.works i u (V y)) x j):
 let _:ℝ→ℝ:=id; let F:=crude Y χ Z; let X:=seatP Y.lightF i; let K p:= stewP Y j (2*j+k) (lushR j Ω r t pu) (checkL Ξ w' u w) (p:Y.Bright).val; let B':= badgeD Y j i K
 Woven (Z i).site X p e (F.view i) ((1+(wag X p.B:ℝ))^(2+p.power*j)*B'):=by
   intro a G C₀ r' B; have he' (U:Config su c)(h:Healthy p.threshold (Z i).support U):Money (G.view i) U v B e j:=by
      constructor; intro E _ _ _ V x hE he; exact King.survey_frame Y Ξ K' hw hp hx i w he (hE.symm ▸ hM ▸ hA i ▸ h) (hP _ V x he) Z hn
   have hG:G.Gather:=plumE Y Z χ hA hp hg hx
   have hh:C₀=(Z i).support:=(hA _).symm
   rw [hh]; refine ⟨hG.sees i,hG.role i,?_,?_,hG.reads i,?_⟩
   · intro U h; rw [hQ]; exact Canvas _ U (he' _ h) he
   · intro U h l hV hp; rw [hQ] at hV; exact vistaQ (C_:=Z i) hQ he ha (he' _ h) (hG.sees _) (hG.role _) hk hz hv l hV hp
   apply mul_nonneg (by positivity); have hh:= he' (1:Config su c) (AnalyticBridge.VerifiedReset.flat_ok ..)
   exact (hh.content ℝ (fun _=>1) 0 rfl (show Mode (fun _:ℝ=>1) 0 j v from ⟨he.le, fun _=> a_oneB _ _ he.le⟩)).2.nonneg
end YM.ConnectedActivityE6.Blaze.King
#print axioms YM.ConnectedActivityE6.Blaze.King.gold_frame
