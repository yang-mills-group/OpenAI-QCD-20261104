import YM.MassiveQCD.Plate.Sight
import YM.MassiveQCD.Charter.Paint

/-! # Lens-specific financial Worts (projected physical spin!)
 Real Hess estimates work on any budgeted Θ fields; can call `News.pays` without precommitting N or split witness.
 Crucial V-clock arithmetic through ALL arity n. Here `Sands.Horn` shape is at the canonical `plate` (LIV mirror), not restricted to orientation averages. `Ψ` may be chosen arbitrarily every call; apply specializing to eraser projections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Lyre
open QCD ConnectedActivityE6 ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Tree.Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N M:ℕ}(Y:Fleet H ι M){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph
open AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff QCD.Stew Plate Sands
open Grass
noncomputable abbrev billL (i:Site c) (a:ℝ):Fields c N→L[ℝ] Fields c N:= (bias (Stew.lens (N:=N) i) a).restrictScalars ℝ
variable (Γ:Cash W s μ L Q o C T (lore R))
variable {τ δ u:ℝ}
lemma rewritten (D:Support c)(o':Site c)(p:BudgetPoint)(f:Grid c→ Lat.Fields c N)(t:ℝ) (he:o'∈D)(hx: p.B=radiusB s)(hp:p.threshold≤2*fiery su s L)(ha:0<τ)(h: Sight D o' 2 p τ f t)(hg:coverNumber p.B D ≤ p.B)(hu: 0≤u) (hh:∀ (U:Grid c),Healthy p.threshold D U → ∀ (M:List (Directions su c)), M.length ≤ p.order → (∀ i∈M,p.dirBound o' i) → (∀ j, ‖M.get j‖ ≤ canopyW su L p.power s) → ∀ Z:Lat.Fields c N→L[ℝ]ℝ, QCD.Spice.rootBill o' τ Z → Eyes ((Z ∘ f) ∘ journey U M.length M.get) u): Sight D o' 2 p τ f u:=by
   refine {h with travels:=hu, pole:=?_}; intro U hU M hM hV
   let i:= RG.leftDerivs f M U; obtain ⟨g,hg',hF⟩:= Dust.commune (X:=billL o' τ i)
   let Z:=g.comp (billL (N:=N) o' τ)
   let V:=Z; let T:= V ∘ f
   have ht: ‖V i‖ = Stew.plank o' τ i :=hF.symm; rw [viewSen _ _ _ ha.le,show Stew.plank o' τ i = ‖V i‖ from ht.symm]
   have hm : Germ p.order T U:= V.contDiff.contDiffAt.comp 0 (h.use U hU)
   rw [show V i = RG.leftDerivs T M U from (Push.Local.left_linear V _ (h.use U hU) hM).symm]
   let L' (s:Directions su c) (i:Bond c):= if i.1∈ D then s i else 0
   let l':= M.map L'; rw [March.stays (g:=T) (fun U V' h'=> congr_arg (Z) (h.room _ _ h')) M L' (fun v hv j hj=> if_pos hj) U U (fun _ _ _=>rfl)]
   have hv (z) (hi:z∈l'): p.dirBound o' z := by
      obtain ⟨i,hh,rfl⟩:=List.mem_map.mp hi; intro b; unfold L'; split; exact hV _ hh b
      rw [norm_zero]; positivity [p.threshold_pos]
   have hc k : ‖l'.get k‖ ≤ canopyW su L p.power s:= by
      have hj:=List.get_mem l' k
      refine pacing _ D ?_ p he rfl (hv _ hj) s L (hx ▸ hg) hp
      obtain ⟨i',hd,hk⟩:= List.mem_map.mp hj; intro k hk'; rw [← hk]; exact if_neg hk'
   have hl : l'.length ≤ p.order := by unfold l'; rw [List.length_map]; exact hM
   change ‖leftDerivs T l' U‖ ≤ u
   have he : leftDerivs T l' U=iteratedFDeriv ℝ _ (T ∘ journey U l'.length l'.get) 0 (cart):= by simpa only [List.ofFn_get] using! Germ.ordered l'.get (hm.prod hl)
   rw [he]; exact (hh U hU l' hl hv hc Z (fun x=> (g.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hg'))).2
lemma occupies {c:Side}{D E:Support c}{o:Site c}{p:BudgetPoint}{f:Grid c→Lat.Fields c N}{a v' K:ℝ}(h:Sight D o k p a f K)(hp:D⊆E)(hx:K≤v') : Sight E o k p a f v':=by
   refine ⟨?_,?_,fun U he=>h.use U (he.mono_left hp),fun i he l hk hV=>(h.pole i (he.mono_left hp) l hk hV).trans hx,h.borel,h.travels.trans hx⟩
   · intro i j hV; exact h.room _ _ (agrees_mono hV (fun _ hv=> hp hv))
   intro U; exact (Creek.regionMon (limitsMon _ _ hp)) (h.gate U) -- inspect
structure Canticle (P':BudgetPoint)(N':Libretto su j)(Γ:Cash W s μ L Q o C T (Sands.lore R))(χ:Chi)(D:Heir.Record) (g:ℝ) (u:ι)(i:ℕ)(wK t t' a:ℝ)(Ψ:EvenA c M→L[ℝ] Lat.Fields c N) : Prop where
    paid : ∀ (F:Forest S.ratio) (q':S.Choices) (V:Grid c) (P:Lat.Fields c N→L[ℝ]ℝ), 0 ≤ g → rootBill (Brim.plate Γ i).site a P→ Healthy P'.threshold (Brim.plate Γ i).support V →
      let W:= homeQ F Γ χ V i q' D; let R':=(lore R).activities.reg i
      Healthy R.p.threshold R'.support W → ∃ v: Grid f→ℝ, LocalOn R'.support v ∧ Measurable v ∧ (∀ U,Healthy R.p.threshold R'.support U → ‖v U‖ ≤wK) ∧ (∀ U,Healthy R.p.threshold R'.support U → BeamRaw R'.support U W g→ ‖P (Ψ (Y.works u U V)) - v U‖ ≤ t) ∧ Sands.Horn P' N' Γ F q' χ D V i v t'
variable {U:Config su c}{Λ ψ t w g A' K' :ℝ}
variable {F':Cash W s μ L Q o C T (Sands.lore R)}{N':Libretto su j}{D:Heir.Record}{P':BudgetPoint}
open AnalyticBridge
variable (hV': Works P L s S T)(he:News P L s W Q o μ C j N' D χ P'.power w u g S.patch) (hp:Plays N' D P' R.p P T s)(hQ:P'.B=radiusB s)
variable (r':ι)(i:ℕ)(hc: Choker Y r' F' i)(M₁: Clusters Y.Bright → RegularAddress c) {Ξ:Utopia H k v d r C' χ}(hO:Oboe H k v B n A b Ξ) (hv:0<v)(hZ:Y.Famous)(hP:Colored Y) (p:Y.Bright)(hY:Aliased Y p r')
variable (Ψ: EvenA c M →L[ℝ] Lat.Fields c N)(t':ℝ)
local notation "A₀"=> Brim.plate F' i
include hp hQ hV' he hc hO hv hZ hP hY
set_option quotPrecheck false
lemma grant (ha:0< a)(η':ℝ)(hA:Sight (Y.fullA p.val) (A₀).site 2 P' a (Ψ ∘ (crude Y χ M₁).view (individual p)) η') (hx:coverNumber P'.B (A₀).support ≤ P'.B)(hK:Canticle Y P' N' F' χ D g r' i Λ t t' a Ψ)(hr:0≤Λ)(ht:0≤t)(hy:0≤t')(h₁:0≤ψ)(hB:t*|w|+Λ*|u|+Hera.lyreFee N' t' D P' R.p L ((lore R).activities.reg i).support (Q.halo+5) s (gStep R.beta) ≤ ψ):
 Sight (A₀).support (A₀).site 2 P' a (Ψ ∘ (crude Y χ M₁).view (individual p)) ψ:=by
   let V:=A₀; let gQ:= (crude Y χ M₁).view (individual p)
   let H' := p.val; have ht':Y.fullA H'=Y.ground r':= (cottage Y p r' hY).2; have hΨ:= hp.rehearsed.temp_eq
   have hR:P'.threshold≤ 2*fiery su s L:= by rw [hΨ,←F'.laws.data.funds.length_eq]; exact F'.laws.data.room.temperatures
   apply rewritten V.support V.site P' _ η' V.anchor hQ hR ha (occupies hA (ht'.symm ▸ hc.pays) le_rfl) hx h₁
   intro U hU LI hL hM hN x hX
   let J:= x.comp Ψ; let Q' :=lore R
   obtain ⟨M,Hm⟩:=globalQ Y r' i hZ hc J
   have hL' : LI.length ≤ j:= hL.trans_eq hp.rehearsed.test
   have h:=he.pays _ _ S T _ F' _ rfl hV' hQ rfl hp i (bridgeX F' i) (by rwa [← hQ]) U M LI hM hU hL' hN
   apply viewL_colored Y χ M₁ LI.get U p r' J (lore R) F' V.support M Ξ hO hv hZ hP hY hc.window hc.pays (hΨ ▸ hU) rfl (fun U V=>Hm V U) (fun F y=> (h F y).2.2.1)
   intro F y; obtain ⟨hz,hx',hH,h⟩:= h F y; obtain ⟨v,hv,hM,hK₀,hT,hQ⟩:= hK.paid F y U x hz hX hU hx'; let v₀ := R.p.threshold
   let A:=((lore R).activities.reg i).support; obtain ⟨Z,hZ,hg⟩:= ticketsH hv hM Λ hr hK₀
   have hl := h Z v hv hZ t ht (fun W he=> ?_); swap
   · by_cases hy: Healthy (lore R).p.threshold A W
     · rw [hZ,masked_eq _ _ _ _ hy,Hm U]; exact hT W hy he
     rw [hZ,masked_ne _ _ _ _ hy,Hm (1:Grid c),hc.home W hy,map_zero,sub_zero,norm_zero]; exact ht
   dsimp only at hl; rw [hg] at hl
   apply earns F F' χ U y LI N' (Q.halo+5) i M D hp hU le_rfl hL' (by assumption) ⟨Z,hy,hZ,hl,hQ⟩ hB
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.grant
