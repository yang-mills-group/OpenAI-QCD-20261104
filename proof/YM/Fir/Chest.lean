import YM.Fir.Shale
/-! Prelude exposures. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} {β e:ℝ}(hp:C.Path β e) {n:ℕ} (G:∀ d,Cottage P d) (hr:Sway C.S) {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
abbrev CellF (d:ℕ):= Stokes d→ℂ
noncomputable abbrev ridgeF (d:ℕ)(i:ℕ) : CellF d →L[ℂ] Label d:= LinearMap.toContinuousLinearMap ((G d).K.ridge i)
structure Sash (G:∀ d,Cottage P d) (φ:ℕ→ℕ) where
   A (u:Averaging)(d:ℕ): Label d →L[ℂ] CellF d
   R(d:ℕ): CellF d →L[ℂ] Label d
   L (d:ℕ): Stokes d → Label d
   plumes (u d): Tendsto (fun i=> (G d).plate u (φ i)) atTop (𝓝 (A u d))
   pearls (d): Tendsto (fun i=> ridgeF G d (φ i)) atTop (𝓝 (R d))
   prices (d): Tendsto (fun i=> (G d).K.g (φ i)) atTop (𝓝 (L d))
-- persistence of inclusion & derivative projection prices
structure DriftF (G:∀ d,Cottage P d) (φ:ℕ→ℕ):Prop where
   views (d:ℕ) (b:Stone d): ∃ Z:ℕ→ CellF (d+1), Brush (G _).E (G _).K (fun i=> stem P d i (lid d b)) Z ∧ ∃ z,Tendsto (Z ∘ φ) atTop (𝓝 z)
   walks (d:ℕ)(b:Stone d)(x:Axis):∃ Z:ℕ→ CellF (d+2),Brush (G _).E (G _).K (fun i=> lDer C i x (stem P d i (lid d b))) Z ∧∃ z,Tendsto (Z ∘ φ) atTop (𝓝 z)
lemma Sash.tuck (s:Sash G φ)(g:ℕ→ℕ)(hg:Tendsto g atTop atTop): Nonempty (Sash G (φ∘g)):=⟨⟨s.A,s.R,s.L,fun u d=> (s.plumes u d).comp hg,fun d=> (s.pearls d).comp hg,fun d=> (s.prices d).comp hg⟩⟩
variable {G} in
lemma DriftF.past (s: DriftF G φ)(g:ℕ→ℕ)(hg:Tendsto g atTop atTop): DriftF G (φ∘g) where
   views d k:= by obtain ⟨V,hv,z,h⟩:=s.views d k; exact ⟨V,hv,z,h.comp hg⟩
   walks d k x:=by obtain ⟨V,hv,z,h⟩:=s.walks d k x; exact ⟨V,hv,z,h.comp hg⟩
include hp hr G hφ
private lemma sails:∃ g:ℕ→ℕ,StrictMono g ∧ DriftF G (φ ∘ g):=by
    let I:= Σ d:ℕ, Stone d
    choose V hV using fun i:I=> cupR hp hr i.1 G (lid i.1 i.2) (i.1+1) (Nat.le_succ _); obtain ⟨g,hg,v,hvg⟩:= Lantern.armor (W:=fun i:I=>CellF (i.1+1)) (fun i=> V i ∘ φ) (fun i=>by obtain ⟨T,hT,t⟩:=(hV i).cost; exact ⟨T,hT,hφ.eventually t⟩)
    choose R hR using fun i:I×Axis=> crossP hp hr i.1.1 G (lid i.1.1 i.1.2) (i.1.1+2) le_rfl i.2; obtain ⟨l,hl,L,hL⟩:= Lantern.armor (W:=fun i:I×Axis=>CellF (i.1.1+2)) (fun i=> R i ∘φ ∘g) (fun i=>by obtain ⟨T,hT,t⟩:=(hR i).cost; exact ⟨T,hT,(hφ.comp hg.tendsto_atTop).eventually t⟩)
    refine ⟨g ∘l,hg.comp hl,⟨fun d k=> ?_,fun d k x=>?_⟩⟩
    · exact ⟨_,(hV ⟨d,k⟩),_,(hvg ⟨d,k⟩).comp hl.tendsto_atTop⟩
    exact ⟨_,hR (⟨d,k⟩,x),_,hL (⟨d,k⟩,x)⟩
set_option maxHeartbeats 300000 in
private lemma fossils:∃ g:ℕ→ℕ, StrictMono g∧ Nonempty (Sash G (φ ∘g)):=by
   let I:=ℕ×Averaging; obtain ⟨g,hg,L,hL⟩:= Lantern.armor (fun (i:I)=> (G i.1).plate i.2 ∘ φ) (fun i=>by obtain ⟨T,hT,t⟩:= (G _).heights hp hr i.2; exact ⟨T,hT,hφ.eventually t⟩)
   haveI (i:ℕ): ProperSpace (CellF i →L[ℂ]Label i):= FiniteDimensional.proper ℂ _
   haveI (i:ℕ): ProperSpace (Stokes i →Label i):= FiniteDimensional.proper ℂ _
   obtain ⟨l,hl,K,hK⟩:=Lantern.armor (fun i=> ridgeF G i ∘φ ∘g) (fun i=>by
       have hx:∀ᶠ k in atTop,‖ridgeF G i k‖ ≤ (G i).K.heightM:= (G i).K.pluck.mono fun k hk=> (ridgeF G i k).opNorm_le_bound (G i).K.h_positive hk
       exact ⟨_,(G i).K.h_positive,(hφ.comp hg.tendsto_atTop).eventually hx⟩)
   obtain ⟨p,hp,X,hX⟩:= Lantern.armor (W:=fun d=>Stokes d → Label d) (fun i=> (G i).K.g ∘ φ ∘g ∘ l) (fun i=>by
       have hv:∀ᶠ k in atTop,‖(G i).K.g k‖ ≤ (G i).K.price:= (G i).K.tall.mono fun k hk=> (pi_norm_le_iff_of_nonneg (G i).K.realH).mpr fun j=>(hk j).1
       exact ⟨_,(G i).K.realH,(hφ.comp (hg.tendsto_atTop.comp hl.tendsto_atTop)).eventually hv⟩)
   exact ⟨_,hg.comp (hl.comp hp),⟨⟨fun u d=>L (d,u),K,X,fun u d=> (hL (d,u)).comp (hl.tendsto_atTop.comp hp.tendsto_atTop),fun d=> (hK d).comp hp.tendsto_atTop,hX⟩⟩⟩
lemma signals :∃ g:ℕ→ℕ,StrictMono g∧Nonempty (Sash G (φ ∘g)) ∧ DriftF G (φ ∘g) ∧∃ Z: SpaceZ,Ability P (φ∘g) Z:=by
    obtain ⟨g,hg,hD⟩:=sails hp G hr hφ; obtain ⟨l,hl,⟨A⟩⟩:= fossils hp G hr (hφ.comp hg.tendsto_atTop); obtain ⟨p,hpv,Z,hZ⟩:= year hp G hr _ ((hφ.comp hg.tendsto_atTop).comp hl.tendsto_atTop); exact ⟨_,hg.comp (hl.comp hpv),Sash.tuck G A p hpv.tendsto_atTop,hD.past _ (hl.tendsto_atTop.comp hpv.tendsto_atTop),Z,hZ⟩
end YM.Massive.Fir
#print axioms YM.Massive.Fir.signals
