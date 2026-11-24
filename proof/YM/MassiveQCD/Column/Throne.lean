import YM.QCD.Purse.Older
/-! # Quantitative pre-L term in the sharp reserve, important for split cone. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Shells
open ConnectedActivityE6 ConnectedActivityE6.Blaze Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side}{j n l k : ℕ} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {O R : BudgetPoint} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B t t' w y u: ℝ}
variable {δ β B₀:ℝ}{Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T (trimP T R δ β B₀)}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {N':Libretto su j}
open Garden Stew Dust Brick YM.Next.Free Jets.Touch Orbit Further Leaf Tee Flume Quarry Pine
open Planned.AtomRegular
open Run Jets Jets.Sun
open Ac Trees Labels Animals Further.ShellBirth49.Fusing Collide
open Trees Ac Further.ShellBirth49.Fusing Collide
open Labels
variable {p i j' m m':ℕ}
lemma stable_throne (u a ψ:ℝ)(p ℓ:ℕ)(N':Libretto su j)(K:Hera.Rights su j)(hu:0<u)(ha:0≤a):∃ C:ℝ, ∃ n:ℕ, 0<C ∧∀ L:Side,n≤L.val→Capstone L ℓ p u a (fern L * C) N' K ψ:=by
    let z:=u/4; have ht:0<z:=by unfold z; positivity
    obtain ⟨C,hC,hM⟩:=boreal N' K p z ψ ht; obtain ⟨g,hg⟩:= Fees.exponent ℓ ht ha (show 2*z<u from by unfold z; linarith)
    let P:= 1+C*Real.exp (a*preCost ℓ); have hp:0<P:=by unfold P; positivity
    refine ⟨P,g,hp,fun L hL=>?_⟩; constructor; intro O h c f D hd n b m' hv hz
    have hz':= hM b m' hv O h; have hQ:= hg c f D (hd.symm ▸ (by omega)); have h1:=Real.exp_monotone (mul_le_mul_of_nonneg_left hz ha); have h2 : Real.exp (z*(m':ℝ))*Real.exp (a*(preCost ℓ+conversion D ℓ * m')) ≤ Real.exp (a*preCost ℓ)*Real.exp (u*m'):=by
       rw [← Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; nlinarith only [hQ.2.2,ht,Nat.cast_nonneg (α:=ℝ) m']
    let p₁:= Real.exp (u*(m':ℝ)); let Q:=Real.exp (a*preCost ℓ); let A:ℝ:= L.val; have hA:0<A:=by unfold A; positivity
    let ε:=fern L*P; have hN: C*Q ≤ ε*A:= by rw [show ε*A=P from ?_]; exact le_add_of_nonneg_left zero_le_one; change A⁻¹* _ * A=_; field_simp
    apply (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hz' (by positivity [fern_pos L])) h1 (Real.exp_pos _).le (by positivity [fern_pos L])) (show 0 ≤ (L.val:ℝ)^4 from by positivity)).trans; change A⁻¹^5*_*_*A^4 ≤_
    rw [←mul_assoc (A⁻¹^5) C,mul_assoc (A⁻¹^5*C)]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity : 0≤ A⁻¹^5*C)) (by positivity : 0 ≤ A^4)).trans
    change A⁻¹^5*C*(Q*p₁)*A^4 ≤ _; rw [←mul_assoc (A⁻¹^5*C),mul_assoc (A⁻¹^5) C]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤A⁻¹^5)) (Real.exp_pos _).le) (by positivity : 0 ≤ A^4)).trans_eq
    unfold ε fern P A; field_simp
end YM.QCD.Shells
