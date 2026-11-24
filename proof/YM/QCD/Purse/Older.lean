import YM.QCD.Purse.Cub
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Entrance
/-! # Real layer. hue dictionaries on arbitrary virtual-τ labels; convert only via corresponding j Tape. -/
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
lemma nails (L:Side):∀ᶠ x in atTop,radiusB x+1 ≤ highR L x+highR L x:=by
    let k:= su.slopeConstant*Real.log L.val
    filter_upwards [(Work.E09.betaF_growth su L).eventually (Stock.stepsize (-k)),(Work.E01.radiusB_tendsto.comp (Work.E09.betaF_growth su L)).eventually_ge_atTop 4] with x hx h
    change radiusB ((x+k)+(-k))^2 ≤ _ at hx; rw [add_neg_cancel_right] at hx
    change radiusB x^2≤2*(highR L x)^2 at hx
    change 4 ≤ highR L x at h
    by_contra! ht; have hh:2*highR L x≤radiusB x:=by omega
    nlinarith
noncomputable def ChargeF (t:ℝ)(l:ℕ):= t⁻¹^l*l.factorial*Real.exp t
lemma boreal (V: Libretto su j)(Z:Hera.Rights su j)(p:ℕ)(u ψ:ℝ)(h:0<u):∃ C₁:ℝ,0 ≤ C₁∧∀ (B R':ℕ) (hp:B ≤R'*9^4)(O:BudgetPoint), O.power=p→ fluteT V Z O ψ B ≤ C₁*Real.exp (u*R'):=by
    let k:=Lute.debited j p; let p':ℝ:=9^4; let m n:=(1+(n:ℝ))^k
    let C:=1+carryFee V Z ψ+Hera.grandFee Z; let R:=Hera.ripple V 1
    have hC:0 ≤ C:=by unfold C; positivity [cin V Z ψ,sinR Z]
    have hR:0 ≤ R:=by unfold R Hera.ripple; positivity [Lute.leading_one V]
    let a:= 2*k; let D:=C*(R*(2*p'^k))*p'^15; let e:=ChargeF u (k+15); have hD:0 ≤D:=by unfold D p'; positivity; -- indent
    refine ⟨2+D*e,le_add_of_nonneg_right (α:=ℝ) (mul_nonneg hD (by unfold e ChargeF; positivity)) |>.trans' (by norm_num),?_⟩
    intro b q hp O hk; have he:1+(b:ℝ)≤p'*(1+(q:ℝ)):=by
       have hv : (b:ℝ)≤ (q:ℝ)*9^4:= by exact_mod_cast hp
       unfold p'; linarith
    have hM: Hera.dueFee V O b ≤ R * (2*p'^k) * (1+(q:ℝ))^k:=by
       unfold Hera.dueFee; rw [hk,mul_assoc R]; apply mul_le_mul_of_nonneg_left _ hR
       have hm':1≤(1+(b:ℝ))^k:=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)); have hz:=(pow_le_pow_left₀ (b:=p'*(1+(q:ℝ))) (by positivity) he k); rw [mul_pow] at hz
       rw [mul_assoc 2]; linarith only [hm',hz, show Lute.debited j p=k from rfl] -- k
    let z:=Real.exp (u*(q:ℝ)); let x:ℝ:=1+q; have hX:0≤x:=by unfold x; positivity
    have ht:0≤C*Hera.dueFee V O b:= mul_nonneg hC (alert ..)
    have ha := polynomial_cost h (show 0 ≤ (q:ℝ) from Nat.cast_nonneg _) (k+15)
    have hz:1≤ z:= Real.one_le_exp (mul_nonneg h.le (Nat.cast_nonneg _))
    unfold fluteT; rw [add_mul (2:ℝ) (D*e),mul_assoc D]
    apply add_le_add (le_mul_of_one_le_right (by norm_num) hz)
    change C*_*(1+(b:ℝ))^15 ≤ _
    apply le_trans _ (mul_le_mul_of_nonneg_left (show x^(k+15) ≤ e*z from ha) hD); rw [pow_add]
    apply (mul_le_mul ((mul_le_mul_of_nonneg_left hM hC)) (pow_le_pow_left₀ (by positivity) he 15) (by positivity) ((mul_le_mul_of_nonneg_left hM hC).trans' ht)).trans_eq; unfold D x; ring
-- reserve.prices before L uses crowd ratio. buys any η budget multiplicative needed e* L^cost incl fees. geometry thought. y shrinking.P.
structure Capstone (L:Side)(ℓ p:ℕ)(A v δ:ℝ)(N':Libretto su j)(K:Hera.Rights su j)(ψ:ℝ):Prop where
    lots : ∀ (O:BudgetPoint), O.power=p →∀ (c f:Side)(F:Ratio c f),F.count=L →∀ n b m:ℕ, b ≤ m*9^4→ (n:ℝ) ≤ preCost ℓ+conversion F ℓ*m →
      fern L^5*fluteT N' K O ψ b *Real.exp (v*n) * (L.val:ℝ)^4 ≤ δ*Real.exp (A*m)
lemma throne (u a ψ ε:ℝ)(p ℓ:ℕ)(N':Libretto su j)(K:Hera.Rights su j)(hu:0<u)(ha:0≤a)(he:0<ε):∃ n:ℕ,∀ L:Side,n≤L.val→Capstone L ℓ p u a ε N' K ψ:=by
    let z:=u/4; have ht:0<z:=by unfold z; positivity
    obtain ⟨C,hC,hM⟩:=boreal N' K p z ψ ht; obtain ⟨g,hg⟩:= Fees.exponent ℓ ht ha (show 2*z<u from by unfold z; linarith)
    obtain ⟨m,hm⟩:=exists_nat_gt (C*Real.exp (a*preCost ℓ)/ε);
    refine ⟨m+g,fun L hL=>?_⟩; constructor; intro O h c f D hd n b m' hv hz
    have hz':= hM b m' hv O h; have hQ:= hg c f D (hd.symm ▸ (by omega)); have h1:=Real.exp_monotone (mul_le_mul_of_nonneg_left hz ha); have h2 : Real.exp (z*(m':ℝ))*Real.exp (a*(preCost ℓ+conversion D ℓ * m')) ≤ Real.exp (a*preCost ℓ)*Real.exp (u*m'):=by
       rw [← Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; nlinarith only [hQ.2.2,ht,Nat.cast_nonneg (α:=ℝ) m']
    let p₁:= Real.exp (u*(m':ℝ)); let Q:=Real.exp (a*preCost ℓ); let A:ℝ:= L.val; have hA:0<A:=by unfold A; positivity
    have hN: C*Q ≤ ε*A:= by rw [mul_comm ε]; exact (div_le_iff₀ he).mp (hm.le.trans (by unfold A; exact_mod_cast (show m≤ L.val by omega)))
    apply (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hz' (by positivity [fern_pos L])) h1 (Real.exp_pos _).le (by positivity [fern_pos L])) (show 0 ≤ (L.val:ℝ)^4 from by positivity)).trans; change A⁻¹^5*_*_*A^4 ≤_
    rw [←mul_assoc (A⁻¹^5) C,mul_assoc (A⁻¹^5*C)]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity : 0≤ A⁻¹^5*C)) (by positivity : 0 ≤ A^4)).trans
    change A⁻¹^5*C*(Q*p₁)*A^4 ≤ _; rw [←mul_assoc (A⁻¹^5*C),mul_assoc (A⁻¹^5) C]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤A⁻¹^5)) (Real.exp_pos _).le) (by positivity : 0 ≤ A^4)).trans_eq
    field_simp
lemma dense (Z:Ratio c f)(O:ι→Site f)(D:ι→ℝ)(p':ℝ)(hD:0 ≤ D)(hp:∀ x,SumBudget (fun i=>if O i=x then D i else 0) p') (x:Site c):SumBudget (fun i=> if Z.parent (O i)=x then D i else 0) ((Z.count.val:ℝ)^4*p'):=by
   apply budget_of_sum (fun i=>ite_nonneg (hD i) le_rfl); intro s; rw [← Finset.sum_filter]; let v:= univ.filter (fun i=> Z.parent i ∈ ({x}: Support c)); have hx:v.card ≤ Z.count.val^4:=by simpa only [Finset.card_singleton,one_mul] using crowd Z ({x}:Support c)
   rw [←Finset.sum_fiberwise_of_maps_to (t:=v) (g:=O) (fun i hi=> mem_filter.mpr ⟨mem_univ _,mem_singleton.mpr (mem_filter.mp hi).2⟩)] -- parameter
   apply le_trans (b:=∑ _∈v,p') (Finset.sum_le_sum fun j _=>?_) ?_; swap
   · rw [sum_filter]; exact budget_sum (hp _) _
   simp only [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hx) (budget_nonneg (hp 0))
end YM.QCD.Shells
