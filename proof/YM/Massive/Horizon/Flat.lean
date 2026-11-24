import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Opals
import YM.Massive.Horizon.Bank
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Sands
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
local notation "ζ"=>radiusB s
open Ursell QCD.GasP Stained March Graph
open AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Lat QCD.Spice
lemma flatView (χ:Chi)(M:Clusters Y.Bright →RegularAddress c)(V:Config su c)(p:Y.Bright)(u:ι)(J:EvenA c N→L[ℝ]ℝ)(R':Rep su f)(F':Cash W s μ L Q o C T R')(Y':Support c)(Q':Eth R' l)
    (Ξ: Utopia H k v d r C' χ)(hΞ:Oboe H k v B n A b Ξ) (hv:0<v)(hZ:Y.Famous)(hP: Framed Y)(hz:Aliased Y p u)(ht:Y.window u= baseRead (R'.activities.reg l).support s S)
    (hr: Y.ground u ⊆ Y')(hV : Healthy (Pressure.temp s) Y' V) (he:R'.beta=R.beta)(hQ:∀ V W,Q'.ingredient V=J (Y.works u V W))
    (hh: ∀ (F:Forest S.ratio) (y:S.Choices), (vary (foyer F' l F χ V y) V).relating.PosDef) (z:ℝ) (hc:∀ F y, ‖cinema l R' Q' (vary (foyer F' l F χ V y) V) o.a (podium S su Y' (radiusB s))-z‖ ≤ a): ‖J ((crude Y χ M).view (individual p) V) -z‖ ≤ a:=by
   have hW:(seatP Y.lightF (individual p)=Y.ground u)∧Y.fullA p.val=Y.ground u:= cottage Y p u hz; have hr:(Y.fullA p.val)⊆ Y':=hW.2.symm ▸ hr
   let D:Slab su c 0:=0; let π:= journey V 0 D; obtain h:= liveryF Y p D hZ hP (hV.mono_left hr) hΞ hv M; let W x:= Y.brisk p.val χ (π x); let v: Reserve S × S.Choices → Panels 0→ ℝ:= fun z x=> cinema l R' Q' (vary (foyer F' l (allot z.1) χ V z.2) (π x)) o.a (podium S su Y' (radiusB s))
   letI : Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
   let C':=Reserve S × S.Choices; let t':Reserve S → S.Choices → ℝ:= fun x y=>v (x,y) 0
   have hA{σ:Type}[Fintype σ][Nonempty σ] (Y:σ→ℝ)(hy:∀ i,‖Y i - z‖ ≤ a): ‖likely Y - z‖ ≤ a:=by
     unfold likely; let n:ℝ:= Fintype.card σ; have hn:0<n:= Nat.cast_pos.mpr Fintype.card_pos
     rw [show _ * _ - z=n⁻¹ * (∑ i, (Y i-z)) from ?_,norm_mul]; swap
     · change n⁻¹ * _ -z=_; rw [Finset.sum_sub_distrib]; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];change _=n⁻¹ *(_- n*z);field_simp
     rw [Real.norm_of_nonneg (inv_pos.mpr hn).le]; exact (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>hy i)) (inv_pos.mpr hn).le).trans_eq (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change n⁻¹*(n*a)=_;field_simp)
   let L:=likely fun (x:Reserve S)=>likely (t' x); have hL : ‖L-z‖ ≤ a:= hA _ (fun x=> hA (t' x) (fun y=> (by simpa only [t',v,π,Planned.AtomRegular.Sample.journey_origin V D] using hc (allot x) y)))
   let X:= (crude Y χ M).view (individual p);
   suffices heX:J (X V)=L from (show ‖J (X V)-z‖≤a from heX.symm ▸ hL)
   have H':=h.self_of_nhds; simp only [Function.comp_apply,Planned.AtomRegular.Sample.journey_origin V D] at H'; unfold X L; rw [H']; unfold Fleet.brisk
   have he {ι:Type}[Fintype ι] (X:ι→ EvenA c N): J (choiceS X)=likely (fun i=> J (X i)):=by unfold choiceS likely; rw [map_smul,map_sum]; rfl
   rw [he]; apply congr_arg likely; funext T'
   let G:=allot T'; let X:= prism T s χ o.K V G; change J (Y.bandL p.val (vary X V))=_; unfold Fleet.bandL; rw [if_pos,he]; rotate_left
   · exact ⟨p.2.1.2.1,p.2.1.2.2⟩ -- edit proof
   apply congr_arg likely; funext y
   rw [← Stained.copyL Y p.val X hZ rfl p.2.2 (hV.mono_left hr), stacksY Y p u hz (k:=l), hW.2,show p.val=_ from hz]
   simp only [t',v,π,Planned.AtomRegular.Sample.journey_origin V D]
   exact (scene Y (vary (foyer F' l G χ V y) V) hZ rfl rfl u Y' J (hW.2 ▸ hr) _ R' ht (by assumption) _ (fun i=> hQ i _) (hh G y)).symm -- phase
variable {U:Config su c}{Λ ψ t w w' t' g:ℝ}
variable {F':Cash W s μ L Q o C T (lore R)}{N':Libretto su j}{D:Heir.Record}{P':BudgetPoint}
variable (hV' : Works P L s S T) (he:News P L s W Q o μ C j N' D χ P'.power w w' g S.patch)
variable (hp:Plays N' D P' R.p P T s)(hQ:P'.B=radiusB s)
variable (u:ι)(i:ℕ)
open AnalyticBridge Stew
variable (hc: Choker Y u F' i)(M₁: Clusters Y.Bright → RegularAddress c) {Ξ:Utopia H k v d r C' χ}(hO:Oboe H k v B n A b Ξ) (hv:0<v)(hZ:Y.Famous)(hP: Framed Y)
variable (p:Y.Bright)(hY:Aliased Y p u)
set_option quotPrecheck false
local notation "Pz"=> Brim.plate F' i
local notation "f4"=>((lore R).activities.reg i).support
local notation "f?"=> Cub.opal N' D P' R.p L f4 (Q.halo+5) s (gStep R.beta)
local notation "e?"=> AnalyticBridge.LocalGaussian.Moments.meter (Lute.heads su R.p L f4 (Q.halo+5) s) 0 D.K (2*((j+1)+(j+1)))
include hp hQ hV' he hc hO hv hZ hP hY
set_option maxHeartbeats 660000 in
lemma flatFunds (hj:1≤ j) (Z:EvenA c N→L[ℝ]ℝ)(K:ℝ) (hh:‖K‖≤Λ) (hx:coverNumber P'.B (Pz).support ≤ P'.B)(hw:Heir.Short S R.p f4)
    (hη: f? ≤1)(hhx:Cub.clocks N' 1 * f? * e? ≤ t') (ht:0≤t) (hK:∀ (F:Forest S.ratio)(y:S.Choices), let W:=homeQ F F' χ (1:Grid c) i y D; let Rb:=(lore R).activities.reg i; 0 ≤ g → Healthy R.p.threshold Rb.support W → ∀ U, Healthy R.p.threshold Rb.support U → BeamRaw Rb.support U W g → ‖Z (Y.works u U (1:Grid c))- K‖ ≤ t) :
    ‖Z ((crude Y χ M₁).view (individual p) (1:Grid c))-K‖ ≤ (t*|w|+Λ*|w'|)+t'*Λ :=by
   let V:=Pz; let A:=(lore R).activities.reg i; let Y₀: Grid c:=1; let α:=f?; let L':List (Directions su c):=[]
   have hU : Healthy P'.threshold (Pz).support Y₀:= VerifiedReset.flat_ok ..
   have hΛ:0≤Λ:=(norm_nonneg _).trans hh
   obtain ⟨M,Hm⟩:=globalQ Y u i hZ hc Z
   have H := he.pays _ _ S T _ F' _ rfl hV' hQ rfl hp i (bridgeX F' i) (by rwa [← hQ]) Y₀ M L' (by simp [L']) hU (Nat.zero_le _) (fun i:Fin 0=>i.elim0)
   apply flatView Y χ M₁ Y₀ p u Z (lore R) F' V.support M Ξ hO hv hZ hP hY hc.window hc.pays (hp.rehearsed.temp_eq ▸ hU) rfl (fun U V=>Hm V U)
   · intro F y; have h:= (H F y).2.2.1.self_of_nhds; rw [Planned.AtomRegular.Sample.journey_origin] at h; exact h
   intro F y; obtain ⟨hz,hx',_,hg⟩:= H F y; let k:=homeQ F F' χ Y₀ i y D;
   let v:= (fun _:Grid f=>K);
   let τ:= (lore R).p.threshold
   obtain ⟨W₀,hW,hW'⟩:= ticketsH (R:=lore R) (j:=i) (x:=v) (fun _ _ _=>rfl) measurable_const Λ hΛ (fun _ _=>hh) -- wrong args Community. R Kurt
   have hm := hg W₀ v (fun _ _ _=>rfl) hW t ht (fun W hW₂=> ?_); swap
   · by_cases hy: Healthy τ A.support W
     · rw [hW,masked_eq _ _ _ _ hy,Hm Y₀]; exact hK F y hz hx' W hy hW₂
     rw [hW,masked_ne _ _ _ _ hy,Hm (1:Grid c),hc.home W hy,map_zero,sub_zero,norm_zero]; exact ht
   let z:= (gStep R.beta); let Ξ:=mapcase F' i F; let B:= Ξ.hymn T z χ 0 y v (Baffle.magic D R.p R.beta χ) 1 Y₀
   have hE : ‖dollarsF F' χ Y₀ i F y M Y₀-B‖ ≤ (t*|w|+Λ*|w'|):=by
      rw [hW'] at hm; have h:= hm.order 0 (Nat.zero_le _); unfold normJ at h; rw [norm_iteratedFDeriv_zero] at h; dsimp only at h; rw [one_pow,mul_one,Planned.AtomRegular.Sample.journey_origin] at h; exact h
   have hg :0<z:= inv_pos.mpr (Real.sqrt_pos.mpr F'.laws.intake.positive) -- cash H binder capital H shadow; use F'
   have hP:‖B-K‖ ≤ t'*Λ:=by
      let p:=Ξ; have hC := Cub.gasket χ 0 y Ξ (1:Grid f) hp (CouplingShape.reg_const K) (AnalyticBridge.VerifiedReset.sup_le (CouplingShape.sup_const K) hh) A.anchor hw hj (Brim.billboard F' (Nat.le_refl _) i) χ hg (F'.laws.data.funds.length_eq.symm ▸ hη) [] (Nat.zero_le 0) (by simp); have hx:Cub.clocks N' Λ=Cub.clocks N' 1 * Λ:=by unfold Cub.clocks Cub.reachBill Cub.devBill; ring
      change ‖B-K‖ ≤ Cub.clocks N' Λ * _ * _ at hC; rw [hx,F'.laws.data.funds.length_eq] at hC; exact hC.trans ((le_of_eq (by ring) : _ ≤ (Cub.clocks N' 1 * f? * e?)*Λ).trans (mul_le_mul_of_nonneg_right hhx hΛ))
   exact (norm_sub_le_norm_sub_add_norm_sub _ B K).trans (add_le_add hE hP)

end YM.ConnectedActivityE6.Blaze.Sands
#print axioms YM.ConnectedActivityE6.Blaze.Sands.flatView
#print axioms YM.ConnectedActivityE6.Blaze.Sands.flatFunds
