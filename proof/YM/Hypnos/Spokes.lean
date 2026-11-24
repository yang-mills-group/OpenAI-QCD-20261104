import YM.Hypnos.Vela
set_option autoImplicit false
noncomputable section
namespace YM.Hypnos
open Filter Function Lattice Wilson Tree RG Pressure Finset MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations Push.SectorMeasure Push.SectorMeasure.Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Coat Blaze.Vine
open Shell Channel

open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Next.SectorChange
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Matrix Census Green Mask Pulse Itinerary Matter Poll Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{β τ C μ W:ℝ} {o: ConnectedActivityE6.Target.Order G W}{Q:ConnectedActivityE6.Target G P} {X:S.Choices} {r u t d A M D:ℝ}{F:Tree.Forest S.ratio}{n:ℕ}

section curls
variable {m:Side}
abbrev marrow (V:Config G m)(p:Cell m):= G.curvature (faceValue V p)
abbrev tide (z:Directions G m) (p:Cell m):= Work.F03.faceCurl p (Flat.labels z)
lemma tide_round (z:Directions G m) (i:Cell m):
    let x:= i.1; let a:=i.2.val.1; let b:=i.2.val.2
    tide z i=z (x,a)+z (x+step a,b)-z (x+step b,a)-z (x,b):=by
    intro x a b; unfold tide faceCurl; rw [← Exterior.fundamental, Flat.collected]; change linkSum z x (square a b)=_
    have he : x+step a+step b -step a=x+step b := by abel
    have h : x+step a+step b + -step a=x+step b := by abel
    simp only [square,linkSum,Step.vec,Step.used, negDir,posDir,Bool.false_eq_true,↓reduceIte,add_zero]
    rw [h,he,add_sub_cancel_right]; abel
lemma tide_sub (x y:Directions G m)(p: Cell m): tide (x-y) p=tide x p-tide y p:=by
    rw [tide_round,tide_round x,tide_round y]; simp only [Pi.sub_apply]; abel
lemma tide_add (x y:Directions G m)(p: Cell m): tide (x+y) p=tide x p+tide y p:=by
    rw [tide_round,tide_round x,tide_round y]; simp only [Pi.add_apply]; abel
lemma tide_smul (r:ℝ)(x:Directions G m)(p:Cell m): tide (r • x) p=r • tide x p:=by
    rw [tide_round,tide_round x]; simp only [smul_add,smul_sub,Pi.smul_apply]
lemma tide_local {x y : Directions G m}(p:Cell m)(h:∀ i:Bond m,i.1∈ touched p→x i=y i): tide x p=tide y p:=by
    rw [tide_round,tide_round]; let a:=p.2.val.1; let b:=p.2.val.2
    have hs : ∀ i, i∈ touched p ↔ i=p.1 ∨ i=p.1+step a∨i=p.1+step a+step b ∨ i=p.1+step b:=by
       intro i; unfold touched; rw [square_corners]; simp [a,b]; tauto
    rw [h (p.1,a) ((hs _).2 (Or.inl rfl)),h (p.1+step a,b) ((hs _).2 (Or.inr (Or.inl rfl))),h (p.1+step b,a) ((hs _).2 (Or.inr <| Or.inr <| Or.inr rfl)), h (p.1,b) ((hs _).2 (Or.inl rfl))]
variable (F:Tree.Forest S.ratio)
lemma tide_slot (V:Directions G c)(p:Cell f): tide (route T V) p=tide (woody T F V) p:=by
    rw [tide_round,tide_round]; let i:=p.2.val.1; let j:=p.2.val.2
    simp_rw [←JointLoad.Heir.harvest T F V]
    have he : p.1+step p.2.val.2+step p.2.val.1=p.1+step p.2.val.1+step p.2.val.2:=by abel
    rw [he]; abel
end curls
open Malachite
variable (X:Coat T F)(Y: Support c) (Z: Web G) (p:Cell f)
variable (b:Directions G c) (z: Air f G) {v:ℝ}
lemma totter (h:HaloV X Y β r u b z)(he:(touched p).image S.ratio.parent⊆Y) (hr:r ≤ Z.radius) :
    let V:= X.input (X.liftA β z)
    ‖marrow V p - (tide (route T b) p+ gStep β • tide (growSeed X z) p)‖ ≤ Z.scale*r^2+Z.scale*u := by
    obtain ⟨w,hp,hi,hS⟩:= h.chosen; intro V'; have hc:0≤Z.scale:= zero_le_one.trans Z.cost
    rw [tide_slot F,← tide_smul];
    have ha : tide (cropSeed X Y z) p=tide (growSeed X z) p:= tide_local p (fun i hi=> if_pos (he (mem_image_of_mem _ hi)))
    rw [tide_smul,← ha,← tide_smul,← tide_add]; unfold marrow
    have hf : faceValue V' p=faceValue (represent (Flat.labels w)) p:=by
        rw [labels_eq]; apply travel_local; intro e h _; exact hi e (he (mem_image_of_mem _ (List.mem_toFinset.mpr h)))
    rw [hf]; refine (norm_sub_le_norm_sub_add_norm_sub _ (tide w p) _).trans (add_le_add ?_ ?_)
    · have hs:= (labels_area w).trans hp; exact (Z.defect _ _ (hs.trans hr)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs _) hc)
    rw [← tide_sub]; exact (Z.linear _ _).trans (mul_le_mul_of_nonneg_left ((labels_area _).trans hS) hc)

-- Normative on all transported.T.E.pick up later
structure State (G : Gauge) where
    web : Web G
    r : ℝ
    m : ℝ
    m_pos : 0 < m
    r_pos : 0< r
    regular : r ≤ web.radius
    cost x : ‖x‖≤r → G.chord (G.lieExp x)≤ m *‖x‖
lemma paid_s (G:Gauge):Nonempty (State G):=by
    obtain ⟨M⟩:= webExists G; obtain ⟨C,r,hc,hr,hh⟩:= chord_chart_cost G
    exact ⟨M,min r M.radius,C,hc,lt_min hr M.pos,min_le_right ..,fun x hx=> hh x (hx.trans (min_le_left ..))⟩
variable (E : State G)
lemma chordal (h:HaloV X Y β r u b z)(hr:r ≤ E.r): let V:= X.input (X.liftA β z); ∀ s: Site f, ∀ w:Walk, (∀ i∈visits s w,S.ratio.parent i∈Y) → G.chord (travel V s w) ≤ w.length*(E.m*r):=by
    obtain ⟨w,hp,hi,hS⟩:= h.chosen; intro V s m hh
    have he : travel V s m= travel (increment 1 w) s m:= by apply travel_local; exact fun i hv _=>hi i (hh _ hv)
    rw [he]; apply travel_chord; intro i; unfold increment; rw [Pi.one_apply, mul_one]; exact (E.cost _ (((norm_le_pi_norm w _).trans hp).trans hr)).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm ..).trans hp) E.m_pos.le)
end YM.Hypnos
#print axioms YM.Hypnos.totter
