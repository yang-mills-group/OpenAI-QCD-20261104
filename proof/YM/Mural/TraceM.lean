import YM.Mural.Enya
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open YM.Next.Free
variable {c f:Side}{j k m:ℕ}
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG
set_option quotPrecheck false
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "L"=> L'.L
local notation "S"=> L'.visit K d
local notation "Ψ"=> sliceL L' d
local notation "M"=> arctic L j
variable {T: Tube su (L'.visit K d)}{T':Teller su}{Q:Target su T'}{v x₀ W μ C:ℝ} {o:Target.Order su W}
variable (x y: Site c)(p q:Site f){N:ℕ}
local notation "Tx"=> texel L' d 0 x p
local notation "Ty"=> texel L' d 0 y q
local notation "Cq"=> cleared p q L' d x y
local notation "Lq"=> loaded p q L' d x y
local notation "Q0"=> (sliceL L' d).embed x
local notation "Yg"=> (sliceL L' d).embed y
local notation "B"=> radiusB x₀
local notation "A₀"=> Lattice.halo B {Q0}
local notation "σt"=> berthD j
variable (hv:separation ((sliceL L' d).embed x) p ≤ arctic L'.L j)(hw:separation ((sliceL L' d).embed y) q ≤ arctic L'.L j)
variable (hp:separation p q≤ berthD j)
variable (hS: (berthD j)*L'.L.val +arctic L'.L j+4*(berthD j)≤ radiusB x₀)
open MassiveQCD MassiveQCD.Plate MassiveQCD.PaletteT QCD.Mural
open MassiveQCD.Apron.Grove Loom Glow
variable {s t p' t₁ t₂ δ β b a y₀:ℝ} {P':Plan k}{X:Run.St f}{P₀:BudgetPoint}{W':ℕ→Atom su 2}
variable (H:Cash W x₀ μ L'.L Q o C T (trimP T P₀ δ β b))(U: Swathe L' d X W' P' t p' s t₁ t₂ m)
noncomputable def veto : Varn f c:=.inl (Q0,some (trunkFt Q0 B)) -- all supports in voter. 
local notation "δb"=> veto (x₀:=x₀) L' d x
local notation "Xg"=> VarnC H U N
noncomputable def shadeM (r:ℂ) (i: Option Rank) (U:Grid f)(W:Grid c):ℂ:= r*cellD i (loaded p q L' d x y U-cleared p q L' d x y W)
variable (r:ℂ)
local notation "C!" i=> shadeM L' d x y p q r i
lemma tile : payT ((S).ratio) B δb= trunkFt Q0 B:=by
    let v:= Q0; change insert v _=_; exact insert_eq_of_mem (halo_subset B {v} (mem_singleton_self v))
lemma pin_board : siteH δb (S).ratio=x:= (Ψ).embed_parent _
lemma cold (V:Grid f)(W:Grid c) : (Xg).works δb V W=0:=by
    change broke U N B _ _=_; unfold broke; have hz: sliceF U N B δb V=0:=by
         change Port.sparkF c N ((N:ℂ)*((chalkF _ Q0 _ B _).re:_))= _; unfold chalkF; have h: trunkFt Q0 B∉ satZip Q0 B:= fun h=> (mem_sdiff.mp h).2 (mem_filter.mpr ⟨mem_univ _,Subset.refl _⟩)
         -- force punch
         simp [sparkF,chipK,h]
    rw [hz,NormedSpace.exp_zero,sub_self]
variable (hM:2* L'.patch.radius < f.val)(θ:ℝ)(κ w b':ℝ)(f₀:ℝ→ℝ)
include hv hw hp hS
lemma kindle (i:Option Rank) : (∀ W, LocalOn ((VarnC H U N).fine δb) (fun U=> shadeM L' d x y p q r i U W)) ∧ (∀ Y:Grid f, LocalOn ((VarnC H U N).window δb) ((shadeM L' d x y p q r i) Y)):=by
   have h : LocalOn (payT ((S).ratio) B δb) (loaded p q L' d x y):=by rw [tile]; exact load_home L' d x y p q hv hw hp hS
   constructor; · intro W X Y hp; exact congr_arg (fun A:Mat=>r*cellD i (A-Cq W)) (h X Y hp)
   intro X Y W h; have hx: apogee x y Y=apogee x y W:=vistaU x x y σt (by rw [separation_self]; omega : separation x x+4*σt ≤ radiusB x₀) (orbitB L' d x y p q hv hw hp) _ _ (agrees_mono h fun i hi=> Loom.marks _ _ _ ((pin_board L' d K x).symm ▸ Corona.halo_mono (show B ≤6*B by omega) (Subset.refl ({x}:Support c)) hi))
   unfold shadeM cleared; rw [hx]
omit hv hw hp
include hS
lemma geometry : coverNumber B ((Xg).ground δb)≤ Animals.ballCost 38:=by
    let X':=δb; have hg:0<B:=by unfold berthD at hS; omega
    let f₁:=Lattice.halo (38*B) {x}
    have h:(Xg).ground δb ⊆ f₁:=by
         intro i hi; obtain ⟨j,hj,hx⟩:=halo_spec.mp hi; obtain ⟨k,hk,hj⟩:=halo_spec.mp hj; obtain ⟨a,ha,rfl⟩:=mem_image.mp hk
         rw [tile L' d K] at ha; obtain ⟨c,hc,hc'⟩:=halo_spec.mp ha; rw [mem_singleton.mp hc] at hc'; have he:= Work.E04.parent_separation Ψ Q0 a; rw [(Ψ).embed_parent] at he
         refine halo_spec.mpr ⟨_,mem_singleton_self x,?_⟩; have hT:= separation_triangle x j i; have hB:=separation_triangle x ((Ψ).parent a) j; change separation ((Ψ).parent a) j ≤ _ at hj; exact hT.trans (show separation x j+separation j i ≤ _ by omega)
    exact (Corona.cover_mono h B).trans (Corona.tile x 38 B hg)
omit hS
variable {uK:ℕ}
local notation "θp"=>fan L (1/4) x₀
variable (hC:∀ X:su.El, ‖colour X-1‖≤ κ*su.chord X)(hL:0 ≤ κ)(hF:Woods T' L'.L o.a f₀ x₀)
variable (hU:∀ (X:Mat)(i j:Hue),‖X i j‖≤ w*‖X‖)(hW:0 ≤ w)
local notation "T0"=> Real.exp (- (Q.relative * Animals.ballCost 38))
noncomputable def news (r:ℂ)(i: Option Rank):=shadeM L' d x y p q r i
variable (ρ:ℝ)(h₁: ‖r‖*w*(fenceCharge j L'.L κ * f₀ x₀) ≤ fundsL L'.L θ x₀ * Real.exp (- (Q.relative *Animals.ballCost 38)))(h₂: ‖r‖*w*(2*(Kit.scale L'.L)^2) ≤ Real.exp (fan L'.L (1/4) x₀*2)*(fundsL L'.L θ x₀ * Real.exp (-(Q.relative*Animals.ballCost 38))))
include hv hw hp hS hM hC hL hF hU hW h₁ h₂
set_option maxHeartbeats 520000 in
lemma kindleT (i:Option Rank): MassiveQCD.Apron.Grove.TrainY L' d K (N:=N) H U (fun _=> Q0) (shadeM L' d x y p q r i) δb θ:=by
    let C:= C! i; obtain ⟨hu,hp'⟩:= Comet.kindle L' d K x y p q (N:=N) hv hw hp hS H U r i -- order
    refine ⟨?_,fun V W=>cold L' d K x H U V W,?_ ,hp',hu,?_,?_⟩
    · exact ((Ψ).embed_parent _).trans (pin_board L' d K x).symm
    · unfold shadeM; cases i with| none=> unfold cellD; fun_prop | some i=>unfold cellD; fun_prop
    · intro i HT V W; change r*cellD _ _= r*cellD _ _; rw [load_frame]
      simp only [show i Q0=1 from HT x,show i Yg=1 from HT y,show colour 1=(1:Mat) from su.mat_one, Matrix.one_mul,star_one, Matrix.mul_one]
    have hη: 0≤ Q.relative:=by unfold Target.relative; linarith only [Q.bound,Q.usable,Q.pos]
    let b:= fundsL L θ x₀; have hb:0 ≤ b:=(fan_pos ..).le; have h(z:Mat): ‖cellD i z‖≤ w*‖z‖:=by cases i; simpa [cellD] using (mul_nonneg hW (norm_nonneg z)); exact hU ..
    refine ⟨b*T0,mul_nonneg hb (Real.exp_pos _).le,?_, ?_,?_⟩
    · rw [mul_assoc b,← Real.exp_add]; apply mul_le_of_le_one_right hb; refine Real.exp_le_one_iff.mpr (?_); have hv: (coverNumber B ((Xg).ground δb):ℝ) ≤ Animals.ballCost 38:=Nat.cast_le.mpr (geometry L' d K x hS H U); linarith only [mul_le_mul_of_nonneg_left hv hη]
    · intro V W; unfold shadeM; rw [norm_mul]; have he: ‖loaded p q L' d x y V-cleared p q L' d x y W‖≤2*scale L^2:=by rw [two_mul]; exact (norm_sub_le ..).trans (add_le_add (load_bound p q L' d x y hM V) (clear_bound p q L' d x y hM W))
      rw [mul_assoc (‖r‖)] at h₂
      exact (mul_le_mul_of_nonneg_left ((h _).trans (mul_le_mul_of_nonneg_left he hW)) (norm_nonneg _)).trans h₂
    intro F X1 hx ht hh z he hp₀; have hi:hF=hF:=rfl; have hvI:¬ Inside x X1.seeds (18*B):= by rw [← pin_board L' d K (x₀:=x₀) x]; exact hp₀ -- rw syntax
    have hE:= Loom.marks δb (S).ratio B; rw [pin_board L' d K x] at hE
    obtain ⟨g,e,hx'⟩:= hF.cloth X1 hx rfl H.laws.data.room hh _ x (X1.liftA β z) hE he hvI
    let U' := X1.input (X1.liftA β z); unfold shadeM; rw [norm_mul]; rw [mul_assoc ‖r‖] at h₁; apply le_trans _ h₁; refine mul_le_mul_of_nonneg_left ((h _).trans (mul_le_mul_of_nonneg_left ?_ hW)) (norm_nonneg _); exact balance L' d K x y p q hv hw hp hS hM hx' hC hF.frames hL
end YM.QCD.Comet
#print axioms YM.QCD.Comet.kindleT
