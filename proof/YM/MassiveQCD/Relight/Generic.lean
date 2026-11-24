import YM.MassiveQCD.Cabaret.Pier
import YM.MassiveQCD.Evolution.ViewPort
import YM.QCD.Finch.Pune
/-! # Rain off flanks. Masks conserved. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Patron
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt Loom Fleet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
open Sway OrbitG Villa Loom Bay Strut
variable {K: EvenA c N→+*EvenA c N}
variable {A : Clusters Y.Bright→RegularAddress c}(X: Chi)
local notation "Z'"=> crude Y X A
local notation "B'"=> claim Y X
variable (A)(hA:∀ i,(A i).support=seatP Y.lightF i)
variable (hf: Y.Famous) (H':Colorful Y)
-- simultaneous trick: recover ALL honest-masked power orientation by one generic x̄ real. No unverified inertia at sparse cancellations. Includes same U all. Use   EqOn.
open MassiveQCD.Analysis.Shelf
local notation "V'"=>EvenA c N
local notation "X'"=>Clusters Y.Bright
-- addenda patch alongside revisit
lemma moments {A:Type*}[NormedAddCommGroup A][NormedSpace ℂ A] {x y:A} {m n:ℕ}
    (h:Set.EqOn (fun z:ℂ=> z^m • x) (fun z:ℂ=>z^n • y) (Metric.ball 0 1)) (s:ℕ→ℂ): s m • x=s n • y:=by
    have hh := AnalyticOnNhd.eq_of_eventuallyEq (show AnalyticOnNhd ℂ (fun z:ℂ => z^m • x) Set.univ from fun _ _=>(analyticAt_id.pow _).smul analyticAt_const) (show AnalyticOnNhd ℂ (fun z:ℂ=> z^n • y) Set.univ from fun _ _=>(analyticAt_id.pow _).smul analyticAt_const) (Eventually.mono (Metric.ball_mem_nhds (0:ℂ) zero_lt_one) (fun i hi=>h hi))
    have hx:x=y:=by simpa using congr_fun hh 1
    subst y; by_cases hk:x=0; · simp only [hk, smul_zero]
    have he: m=n:= (pow_right_strictMono₀ (by norm_num : 1 < (2:ℝ))).injective (by exact_mod_cast (show (2:ℂ)^m =2^n from smul_left_injective _ hk (congr_fun hh (2:ℂ))))
    rw [he]
variable (z:ι→ℕ)[Countable (Clusters Y.Bright)] (p:ℂ→ι→Grid f→Grid c→EvenA c N)
local notation "Z(" x ")"=> tintF Y (p x)
variable (he:∀ x:ℝ, |x|<1 → ∀ i U V,p x i U V=(x:ℂ)^z i • Y.works i U V) (hg:∀ x:ℝ,|x|<1→ (tintF Y (p x)).Famous ∧ Colorful (tintF Y (p x)))
local notation "w!"=> depthT Y z
include he hg
lemma relight (K:Strut c):∃ e:Equiv.Perm (Clusters Y.Bright),∀ (α:ℕ→ℂ) (i: X') (V:Grid c), spice K (α (depthT Y z i) • Y.honest X (sky K V) i)= α (depthT Y z (e i)) • Y.honest X V (e i):=by
   let t:= spice (N:=N) K; let s (i:X'× X')(x:Grid c) (z:ℂ):= z^(w! i.1) • t (Y.honest X (sky K x) i.1); let w (i:X'× X')(x:Grid c) (z:ℂ):= z^(w! i.2) • Y.honest X x i.2
   obtain ⟨x,hx,ht⟩:= MassiveQCD.Analysis.Shelf.generic s w (fun i j k _=>(analyticAt_id.pow _).smul analyticAt_const) (fun i j k _=>(analyticAt_id.pow _).smul analyticAt_const); let y:=Z( (x:ℂ) ); obtain ⟨hf,hY⟩:=hg x hx
   obtain ⟨π,e,hπ⟩:= hY.travel K (sat K) (ink K) (assured _); let E : Equiv.Perm (X'):= Patron.pack (adawn y (p:=K) hπ)
   have hp (i : X')(V:Grid c): Set.EqOn (s (i,E i) V) (w (i,E i) V) (Metric.ball 0 1):=ht _ (fun V=>?_ ) V; swap
   · let U:=sky K V; have hh (i:X')(V:Grid c): y.honest X V i=(x:ℂ)^(w! i) • Y.honest X V i:= paysS Y z (x:ℂ) (p x) X (he x hx) i V
     have hv : t (y.honest X U i)= y.honest X V (E i):=gistE y (p:=K) hπ hf ..; rw [hh,hh] at hv
     exact (swayC ..).symm.trans hv -- order
   refine ⟨E, fun α i V=> (swayC ..).trans (moments (hp i V) α)⟩
variable (α:ℕ→ℂ)
open Finch Calm Grove
lemma parade (h:∀ V:Grid c,Summable fun i:Clusters Y.Bright=> α (depthT Y z i) • Y.honest X V i) (V:Grid c): potion (fun V=> ∑' i:X',α (w! i) • Y.honest X V i) V = ∑' i:X', α (w! i) • Y.honest X V i :=by
    refine unSpin V fun k=>?_; obtain ⟨e,hS⟩:= relight Y X z p he hg k; let t (V:Grid c)(i:X'):= α (w! i) • Y.honest X V i; exact (((h _).hasSum.map (spice k) (phare _)).tsum_eq).symm.trans ((tsum_congr (fun i=> hS α i V)).trans (e.tsum_eq (t V)))
end YM.QCD.Patron
#print axioms YM.QCD.Patron.parade
