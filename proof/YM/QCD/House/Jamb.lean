import YM.QCD.House.Apace

/-! # Forest purchases and wash budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
set_option quotPrecheck false
local notation "B"=>radiusB τ
variable {w: Reserve S→ ι→ℝ} {p:ι→ℝ}{b:Costs}{u d' z η t h':ℝ}
variable (h:Y.Leaps w b p u)
include h
abbrev apple (b:Costs):= b.rootHit * (1-b.q)⁻¹
lemma dusk_hit {a:ℝ} (ht:0≤a)(hv:a≤ b.exponent): Ac.Hit Y.broad (radiusB τ) (GasP.taxed Y.invD (fun i=> Y.grass w b i.val) (Real.exp b.markSeed)) a (apple b):=by
    intro x; have he:=(cohort Y h x); have hv':=budget_pull (fun i:Y.Dark=>i.val) Subtype.val_injective he -- sig
    refine budget_mono hv' (fun i=>?_) ?_
    · unfold taxed; split; swap; · exact le_rfl
      exact mul_nonneg (mul_nonneg (by positivity) (Y.nonC h i.val)) (Real.exp_pos _).le
    intro i; split
    next hi=> dsimp only; rw [if_pos (show x∈Y.fullA i.val from hi), if_pos i.2.1.2.1]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (Y.nonC h i.val)); apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg (coverNumber _ _))
    next _=> exact hv'.1 _
lemma dawn_hit {a:ℝ} (ht:0≤a)(hv:a≤b.exponent): Ac.Hit Y.lightF (radiusB τ) (fun i=> Y.grass w b i.val) a (apple b):=by
   intro x; have hh:=Y.cohort h x; have h' :=budget_pull (fun i:Y.Bright=>i.val) Subtype.val_injective hh
   refine budget_mono h' (fun i=>?_) (fun i=>?_)
   · split; exact mul_nonneg (Y.nonC h _) (Real.exp_pos _).le; exact le_rfl
   split; next hi=> dsimp only; rw [if_pos (show x∈Y.fullA i.val from hi),if_pos i.2.1.2.1, i.2.2,card_empty,pow_zero,one_mul]; apply mul_le_mul_of_nonneg_left _ (Y.nonC h _); apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _)
   next _=> exact h'.1 _
lemma ceremony {d:ℝ}(hd:0≤d)(hv:d+t≤ b.exponent)(ht:0<t)(he:0<apple b)(hh:degreePrice (radiusB τ) (apple b) t ≤ h') (hz:h'<1): Ready Y.lightF (radiusB τ) (fun i=> Y.grass w b i.val) d (apple b) t h':=⟨he,ht,hh,hz,fun i=> (Y.nonC h i.val),dawn_hit Y h (by linarith) hv⟩
lemma dusk_nn (a:Reserve S) (z:ℝ) (hz:z≤ b.exponent)(hv:0≤z): Summable fun i:Y.Dark=>Y.grass w b i.val :=by
   have hb:= dusk_hit Y h hv hz; let D a:= Y.grass w b (a:Y.Dark).val; let X:=taxed Y.invD D (Real.exp b.markSeed);
   have hx i:0≤ X i:= mul_nonneg (by positivity) (Y.nonC h _)
   have he:= Product.everyone_ne Y.broad (radiusB τ) hx (fun i _=>i.2.1.1) hb; apply he.2.1.of_nonneg_of_le (fun i=> Y.nonC h _) ?_
   intro i; unfold Ursell.charge; have hm := Real.one_le_exp (show 0 ≤ b.markSeed from (h a).1.green.marked); refine le_trans (b:=X i) ?_ ?_
   · exact le_mul_of_one_le_left (Y.nonC h i.val) (one_le_pow₀ hm)
   exact le_mul_of_one_le_right (hx i) (Real.one_le_exp (mul_nonneg hv (Nat.cast_nonneg _)))
omit h
abbrev ShellK (Y:Fleet H ι N):=Y.Dark⊕Support c
abbrev Wort (Y:Fleet H ι N):=Finset Y.ShellK
abbrev Faber (Y:Fleet H ι N):={s: Y.Wort // GasP.wagon Y.broad s}
def furnace (χ:Chi)(V:Grid c) (u:Clusters Y.Bright):=termP (blocked Y.lightF) (fun i=> Y.brisk i.val χ V) u
def honest (χ:Chi)(V:Grid c) (s:Clusters Y.Bright):= masked (Pressure.temp τ) (seatP Y.lightF s) (fun V'=>Y.furnace χ V' s) V
def mission (χ:Chi)(V:Grid c)(s:Y.Wort):= motto Y.broad Y.invD Y.lightF (RG.flags (Pressure.temp τ) V) (Y.duskV χ V) (Y.dawnV χ V) s
lemma phoenix (χ:Chi)(V:Grid c)(hp:Y.Famous)(s:Clusters Y.Bright):Y.honest χ V s=termP (blocked Y.lightF) (Y.dawnV χ V) s:=by
    unfold honest; let T:=seatP Y.lightF s; let t:=Pressure.temp τ
    have he i:Y.dawnV χ V i=masked t (Y.lightF i) (Y.brisk i.val χ) V:= congr_fun (Y.wholeC _ _ hp i.2.2) V
    by_cases hh: Healthy t T V
    · rw [masked_eq _ _ _ _ hh]; unfold furnace termP; apply congr_arg; apply congr_arg; refine prod_congr rfl (fun i _=>?_) ; rw [he, masked_eq]
      exact Finset.disjoint_of_subset_left (subset_biUnion_of_mem (Y.lightF ∘ s.2) (mem_univ i)) hh
    rw [masked_ne _ _ _ _ hh]; rw [Healthy,not_disjoint_iff] at hh; obtain ⟨v,hv,ht⟩:=hh; obtain ⟨i,hi,hv⟩:=mem_biUnion.mp hv; unfold termP; rw [prod_eq_zero hi (show Y.dawnV χ V (s.2 i)=0 from (he _).trans (masked_ne _ _ _ _ (not_disjoint_iff.mpr ⟨v,hv,ht⟩))), smul_zero,smul_zero] -- edit

lemma liftsM (χ:Chi)(V:Grid c)(v b:ℝ) (hv: Summable (fun i=> ‖termP (blocked Y.lightF) (dawnV Y χ V) i‖)) (s:Y.Wort): wearK c N v (Y.mission χ V s)=motto Y.broad Y.invD Y.lightF (RG.flags (Pressure.temp τ) V) (wearK c N v ∘ (duskV Y χ V)) (wearK c N v ∘ dawnV Y χ V) s:=by
   unfold mission motto; let V':=wearK c N v; split; swap; · exact map_zero _
   rw [map_prod]; apply prod_congr rfl; intro i _; rcases i with i|i; · rfl
   change V' (NormedSpace.exp _-1)= NormedSpace.exp _-1
   rw [map_sub,map_one,NormedSpace.map_exp V' (songT v (c:=c) (N:=N)).continuous,map_neg]; apply congr_arg₂ (·-·) _ rfl; apply congr_arg; apply congr_arg
   let Z:=songT v (c:=c) (N:=N); have hh : Summable (fun j: Clusters Y.Bright=> if GasP.seatP Y.lightF j=i then termP (blocked Y.lightF) (Y.dawnV χ V) j else 0):= somG hv _
   unfold portion; change Z (∑' j, if GasP.seatP Y.lightF j=i then _ else _) = ∑' j, if GasP.seatP Y.lightF j=i then _ else _; rw [Z.map_tsum hh]
   exact tsum_congr (fun j=> by split; exact transportTerm Y v V χ j; exact map_zero Z)

include h
set_option maxHeartbeats 850000 in
lemma awardW {μ t e v ν a:ℝ}(hp:Y.Feasible)(hF:Y.Famous)(hk:0<u)(he:0≤a)(ht:0<t)(hz:a+t≤b.exponent)(hq:Ready Y.lightF (radiusB τ) (fun i=> Y.grass w b i.val) (a+t) (apple b) e v)(hh:degreePrice (radiusB τ) μ t ≤ ν)(hu:0<μ)(hx:ν<1)(hr:apple b*(1-v)⁻¹≤1)(hi: apple b + Real.exp 1*(apple b*(1-v)⁻¹)≤ μ)(χ:Chi)(V:Grid c):
   let r₁ (i:Y.Dark):= grass Y w b i.val; let r₂ (i:Y.Bright):= grass Y w b i.val
   let w':= ward Y.broad Y.invD Y.lightF (RG.flags (Pressure.temp τ) V) (duskV Y χ V) (dawnV Y χ V)
   let g:= honest Y χ V
   let s:= mission Y χ V
   Summable g ∧ Summable w'∧ HasSum (fun i=> Y.emergingF i χ V) (NormedSpace.exp (∑' i,g i)*∑' i,w' i) ∧ (∀ i:Y.Wort, ‖token c N u (s i)‖ ≤ tenderW Y.broad Y.lightF i r₁ r₂) ∧
    Ac.Hit (wound Y.broad) (radiusB τ) (taxed (sweep Y.invD) (fun i=> tenderW Y.broad Y.lightF i r₁ r₂) (Real.exp b.markSeed)) a (μ*(1-ν)⁻¹) :=by -- Faber.K w' word clothes
    intro r₁ r₂ w' g s; have hg:g=termP (blocked Y.lightF) (Y.dawnV χ V):= funext (Y.phoenix χ V hF)
    let i: Reserve S := fun _=> Classical.choice (Tree.select S.ratio S.patch.odd_side)
    have hm:= dusk_hit Y h (add_nonneg he ht.le) hz
    have hV i:‖wearK c N u (duskV Y χ V i)‖ ≤ r₁ i:=Y.localP h χ V i.val
    have h₁ := (dusk_nn Y h i _ (he.trans (le_trans (by linarith : a≤a+t) hz)) le_rfl).of_nonneg_of_le (fun j=> norm_nonneg _) hV
    have hX i: ‖token c N u (Y.dawnV χ V i)‖≤ r₂ i:= Y.localP h χ V i.val
    rw [hg]; obtain ⟨h2,h3,h4⟩:= Y.latest u hp hk χ V hq (by linarith) ⟨∑' i, ‖token c N u (Y.duskV χ V i)‖,fun i=>norm_nonneg _,h₁,le_rfl⟩ hX
    refine ⟨h2,h3,h4,fun i=>?_, GasP.inheritsK Y.broad Y.invD Y.lightF (leaflet Y.broad Y.invD Y.lightF (fun i=>i.2.1.1) hq he ht (fun j=>Y.nonC h _) hm (Real.one_le_exp (h i).1.green.marked) hi hu hh hx) he (bookD Y)⟩
    let f₀ (x:Y.Dark):= wearK c N u (Y.duskV χ V x); let g₀ (x:Y.Bright):= wearK c N u (Y.dawnV χ V x); let W₀:= RG.flags (Pressure.temp τ) V
    have he : ‖GasP.motto Y.broad Y.invD Y.lightF W₀ f₀ g₀ i‖ ≤ _ := GasP.boothK Y.broad Y.invD Y.lightF W₀ f₀ g₀ hq (fun i=> (show _ from i.2.1.1)) (by linarith) hr hV (show ∀ z', ‖g₀ z'‖≤ r₂ z' from hX) i
    have hδ : wearK c N u (s i) = GasP.motto Y.broad Y.invD Y.lightF W₀ f₀ g₀ i := Y.liftsM χ V u 0 h2.norm i
    exact Eq.trans_le ((skill u _).trans (congr_arg _ hδ)) he
end YM.QCD.Loom.Fleet
