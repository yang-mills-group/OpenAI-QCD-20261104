import YM.Poised.Pollen
import YM.QCD.Fawn.Price
/-!
# Charter interior, picks real Crown.
Shrink discharged D.ε at furnishing before actual x height. Allows full-rank path cost with constant output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open QCD QCD.Lat QCD.Kit QCD.Grass QCD.Brick QCD.Cove QCD.Stew ConnectedActivityE6.Blaze Push.Uniform UV Cylinder SourceRead
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {B :Type}[Fintype B] {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio}
    {P R : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v s u u₁ u₂: ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j q₀ : ℕ} {D : Slab su c l} {q : Chi} {d : ℝ} {V' : Config su f → Lat.Fields f 6}
namespace Fountain
open Pipes
local notation "Y'"=> Fields f 6 -- remove amb
structure ScrollX (C: Libretto su n)(α A:ℝ)(q₀ K:ℕ)(Pt:Teller su):Prop where
   pos:1≤A
   flow : ∀ {c f:Side}(S:StepData c f)(R:BudgetPoint)(T:Tube su S)(x:Support f)(b:Cover)(U:Directions su c)(_ : Pt.Funds S T) (_: R.power=K)(_ : Odd S.patch.L.val), Limb R.power (S.ratio.parent (wrap f b)) U (2*C.C*R.threshold) →∀ {B:Type}[Fintype B](u : Faces (Site f)→ℝ)(v:B→ℝ), Heritage R x b u v q₀ (route T U,0) (Kit.slope S.patch.L) A
lemma holders (C₀:Libretto su n) (α:ℝ)(Pt:Teller su)(K r q:ℕ)(hk:r ≤ K)(hr:r ≤ Pt.j-2)(hq:q≤2*r+2) : ∃ A:ℝ, ScrollX C₀ α A q K Pt:=by
   obtain ⟨A,hA,H⟩:= Pipes.initial Pt r K _ (mul_pos (a:=2) (by norm_num) (zero_lt_one.trans_le C₀.C_one)) hk hr
   refine ⟨A,⟨hA,?_⟩⟩; intro c f S R T X b U hv hx he hL I _ u v
   rw [hx] at hL; exact H _ _ _ _ _ _ hv hx he b U hL q hq u v -- `..` greedy
variable (a:Museum F x A X Y I)[Fintype I] {C: Libretto su n}{E: Heir.Record}
variable (hp:Plays C E P R Pt T x) (b:Cover) (hw:wrap f b∈X) (hg :Canvas P (S.ratio.parent (wrap f b)) (reach x) V g n C.C)
variable (hO:Short S R X)(hn:2≤n)(hV: Healthy P.threshold Y V) (U:Grid f)(z: Prices su I)(hu:0≤u) (hv:u*‖tape z‖≤ E.ε*R.threshold)(hl:l≤n) (hD:∀ i,P.dirBound (S.ratio.parent (wrap f b)) (D i))
set_option quotPrecheck false
local notation "L"=> S.patch.L
local notation "O"=> S.ratio.parent (wrap f b)
local notation "X₀"=> enters V (S.ratio.parent (wrap f b)) (reach x) g D (a.extra g u z)
local notation "Z₀"=> launch V (S.ratio.parent (wrap f b)) (reach x) g D
local notation "V₀"=> Heir.loom P (reach x) C.C
local notation "b'"=> Kit.slope S.patch.L
variable {p p₀ :ℕ}{I₀ I₂ χ R₁ :ℝ}
variable (he:ScrollX C χ I₀ q₀ p Pt)(hPt:Pt.Funds S T)(hτ:R.power=p)(hE: clinicFee n E.Q*(loom P (reach x) C.C)^2 + E.ε*R.threshold ≤ (Kit.slope S.patch.L)^max q₀ 2 * R.threshold)
include he hPt hp hτ hn hg hD hl hu hv hE -- k issue inclusion
lemma days (w:Faces (Site f)→ℝ)(W:B→ℝ)(j:ℕ)(hj:j≤ n)(v:Fin j→Panels l)(hx:∀ i,‖v i‖≤1) : Heritage R X b w W q₀ ((iteratedFDeriv ℝ j (display T F x k true ∘ X₀) 0 v),0) b' (1+I₀):=by
   let p:= X₀
   have hr:=hp.rehearsed.tensions; have he':= hp.rehearsed; let f':=iteratedFDeriv ℝ j (Z₀) 0 v; let t:=route T f'; have hm:C.C ≥1:=C.C_one; have hκ:1≤ E.Q:=E.majorant; have hb:0≤ V₀:=by unfold loom; positivity [P.threshold_pos]
   have hC: V₀ ≤1 := (le_mul_of_one_le_left hb E.majorant).trans (hr.small.trans (min_le_right ..))
   have hy := he.flow S R T X b f' hPt hτ S.patch.odd_side (launch_cost hg hr.coarse he'.temp_eq he'.powers hm hl hD hC hj v hx) w W
   let Y:= iteratedFDeriv ℝ j (display T F x k true ∘ p) 0 v; let Z:= mainStroke T F true (iteratedFDeriv ℝ j p 0 v)
   have he₁:=a.extra_size g u hu z; have hQ: ‖a.extra g u z‖ ≤ E.ε*R.threshold:=he₁.trans hv
   have ht : ‖Y-Z‖ ≤ clinicFee n E.Q*V₀^2:=by simpa only [spine_self,one_pow,mul_one] using (timesEnter hg (hp.acts F k) he'.temp_eq hn hD hm hl hκ hC hr.allows.le (hQ.trans hr.noise) true).2 j hj v hx
   obtain ⟨hL,h₁⟩:= boxed1 L
   refine Pipes.patchup R X b w W b' 1 Y t ?_ hL h₁ zero_le_one hy
   have hpiV : ‖Z-t‖≤ E.ε* R.threshold:=by
       by_cases he:j=0; · subst j; unfold Z t f'; rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply]; exact (by change ‖(route T (Z₀ 0)+a.extra g u z)-route T (Z₀ 0)‖ ≤ _; rw [add_sub_cancel_left]; exact hQ)
       unfold Z p; rw [enter_pos hg hj (by omega)]; change ‖(t+0)-t‖ ≤ _; rw [add_zero,sub_self,norm_zero]; positivity [E.guards,R.threshold_pos]
   rw [one_mul]; refine ⟨by positivity,fun i=>?_⟩; apply (norm_le_pi_norm ..).trans; apply (norm_sub_le_norm_sub_add_norm_sub Y Z t).trans ((add_le_add ht hpiV).trans (hE.trans ?_)); apply mul_le_mul_of_nonneg_left _ (by positivity); exact le_mul_of_one_le_right R.threshold_pos.le (one_le_pow₀ (by simp))
omit he hPt hp hτ hn hg hD hl hu hv hE
private lemma thirstyW (P:BudgetPoint)(b:Cover)(U:Support f)(g : B→ℝ)(k p:ℕ)(LL:Side)(w:ℝ)(u:ℝ)(hW:0≤w): Heritage P U b (purseX (wrap f b) p u) g k (0:Pipes.Path f B) (Kit.slope LL) w:= residual P U b _ _ _ (inR_R b _ _ _ _ ⟨mul_nonneg hW (pow_nonneg (boxed1 LL).1.le _),fun i=>by change (∑ j, ‖orderR _ g (0:VectorD (Site f) B) i j‖)≤ _; simp only [orderR,Pi.zero_apply,mul_zero,norm_zero,Finset.sum_const_zero]; exact mul_nonneg hW (pow_nonneg (boxed1 LL).1.le _)⟩) hW (boxed1 LL).1 (boxed1 LL).2
variable (f₀:ℝ)(w:B→ℝ)(Z:VectorD (Site f) B)(hX:∀ i,0 < w i)(hF:0<f₀) (ht:Heritage R X b (purseX (wrap f b) p₀ f₀) w q₀ (0,Z) (Kit.slope S.patch.L) I₂) (h1: 1≤I₂)
variable (ζ:ℝ)(hc:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x ζ) (hb : (1+patterns n)*(ζ*(C.M*loom P (Heir.reach x) C.C))*((Fintype.card Pipes.Shell:ℝ)*pup q₀ I₂ * (Kit.slope S.patch.L)^2) ≤ (Kit.slope S.patch.L)^max q₀ 2) (hM:C.M*loom P (Heir.reach x) C.C ≤1)
include hp he hPt hg hτ hn hD hb ht h1 hc hM hF hX hE hu hv hl
set_option maxHeartbeats 560000 in
lemma vesper : -- dummy; shorten
    let Y(y:Panels l): Path f B:= (display T F x k true (X₀ y),hailC (sealsZ (φ T F true (launch V (S.ratio.parent (wrap f b)) (reach x) g D y))) Z)
    ContDiffAt ℝ n Y 0∧ ∀ j:ℕ,j ≤ n → ∀ v: Fin j→Panels l,(∀ i,‖v i‖≤1) → Heritage R X b (purseX (wrap f b) p₀ f₀) w q₀ (iteratedFDeriv ℝ j Y 0 v) (Kit.slope S.patch.L) (1+I₀+(1+I₂)):=by
    intro Y
    let B0 := display T F x k true ∘ X₀; let U y:= φ T F true (Z₀ y); let c:Pipes.Shell := Sum.inl 0; let V':= diffQ U Z; let P0(y:Panels l):= V' y+Z
    have hφ: Through n U 0 (C.M*loom P (Heir.reach x) C.C):= Dust.taxes C hp hg (by omega) hD hl
    have htV:ContDiffAt ℝ (↑n) V' 0 := diff_live Z ζ _ hφ hM (by omega) hc
    have hO : Y=fun y=>(B0 y,P0 y):=by funext y; simp only [Y,P0,V',diffQ,sub_add_cancel]; rfl
    have hW₀:= hp.rehearsed.tensions
    have hV0: ContDiffAt ℝ (↑n) B0 0:= (timesEnter hg (hp.acts F k) hp.rehearsed.temp_eq hn hD C.C_one hl E.majorant (le_trans (le_mul_of_one_le_left (by unfold loom; positivity [C.C_one,P.threshold_pos]) E.majorant) (hW₀.small.trans (min_le_right ..))) hW₀.allows.le ((a.extra_size g u hu z).trans (hv.trans hW₀.noise)) true).1
    have hP : ContDiffAt ℝ n P0 0:= htV.add contDiffAt_const
    rw [hO]; refine ⟨hV0.prodMk hP,fun i hi v hh=>?_⟩
    let A:= iteratedFDeriv ℝ i B0 0 v; let A' := iteratedFDeriv ℝ i P0 0 v
    have he₀:= days (k:=k) a hp b hg hn z hu hv hl hD he hPt hτ hE (purseX (wrap f b) p₀ f₀) w i hi v hh
    let Vq:=purseX (wrap f b) p₀ f₀
    rw [iteratedFDeriv_prodMk hV0 hP (Nat.cast_le.mpr hi)]
    change Heritage R X b Vq w q₀ (A,A') _ _
    rw [show ((A,A'):Path f B)= (A,0)+(0,A') from (by simp)]
    apply Heritage.plusK _ _ _ _ _ _ _ he₀; let hB:=boxed1 L
    let Z' := iteratedFDeriv ℝ i V' 0 v; let G:=iteratedFDeriv ℝ i (fun _:Panels l=>Z) 0 v
    have hY': A'=Z'+G:=by rw [show A'= (iteratedFDeriv ℝ i (V'+fun _=>Z) 0) v from rfl, iteratedFDeriv_add_apply (htV.of_le (Nat.cast_le.mpr hi)) contDiffAt_const]; rfl
    have hx : SeatD Vq w Z (pup q₀ I₂ * b'^2):= (Heritage.purse R X b (0,Z) Vq w hB.1 hB.2 h1 ht).2
    have hZ:SeatD Vq w Z' ((1:ℝ)*b'^max q₀ 2):= SeatD.less _ _ _ _ _ (line_cost Z ζ _ hφ hM (by omega) hc p₀ _ w hF hX hx i hi v hh) (by rw [one_mul]; rw [mul_assoc (Fintype.card Pipes.Shell:ℝ)] at hb; exact hb)
    rw [hY',show ((0,Z'+G):Path f B)=(0,Z')+(0,G) from by simp]; apply Heritage.plusK _ _ _ _ _ _ _ (residual _ _ _ _ _ _ (inR_R b _ _ _ _ hZ) zero_le_one hB.1 hB.2)
    by_cases hx:i=0; · subst i; rw [show G=Z from iteratedFDeriv_zero_apply ..]; exact ht
    unfold G; rw [iteratedFDeriv_const_of_ne hx]; exact thirstyW R b X w q₀ p₀ _ _ _ (zero_le_one.trans h1)
omit hp he hPt hg hτ hn hD hb ht h1 hc hM hF hX hE hu hv hl
variable (YJ:Grid f→Lat.Fields f 6)(nf m₀:ℕ) -- remove
variable (χ₀ : TaperHol) (hG : ∀ k U,slots 6 k (YJ (gauge k U))=YJ U) (heV:Ease.Charm R X YJ) (hS:∀ U,YJ U∈ Creek.region (limits X)) (hB:∀ U,YJ U ∈ layer (Faces (Site f)) nf)(hvF: ∀ (J:Labels.Jet su)(t:ℕ),t<q₀ →WardBin.leading t (Beacon.moment (d:=m₀) χ₀ b J YJ)=0)
set_option quotPrecheck false
local notation "pⁱ"=> purseX (wrap f b) p₀ f₀
variable (hh:R.supBounds (wrap f b) X (framesF (purseX (wrap f b) p₀ f₀) ∘ YJ) τ)(Vb:Hera.Rights su n) (hy:m₀≤R.order)(hm:q₀ ≤ m₀+1)(hx₀:q₀≤2*n)
include hp he hPt hg hτ hn hD hb ht h1 hc hM hF hX hE hu hv hl
include hO hw hV hG heV hS hB hvF hh χ₀ Vb hy hm hx₀
abbrev tithy(nf:ℕ)(I₀ I₂:ℝ)(Vb:Hera.Rights su n)(q₀:ℕ):= patterns n*((n+1:ℝ)*Pipes.central Vb (1+I₀+(1+I₂)) nf q₀)
set_option maxHeartbeats 510000 in
lemma tableau : let V'(x:Panels l):= YJ (gauge (g∘ S.ratio.parent) (a.received k T q d u (journey V l D x) U z))
   let W(x:Panels l):= framesF w (changeVars Z (V' x))
   Through n W 0 ((tithy nf I₀ I₂ Vb q₀)*τ*b'^q₀):=by
    intro V' B₀
    have hκ :1≤I₀:= he.pos
    let U0:= launch V (S.ratio.parent (wrap f b)) (reach x) g D
    let V₂ y:= φ T F true (U0 y) -- remove
    let Y(y:Panels l):Path f B:= (display T F x k true (X₀ y),hailC (sealsZ (V₂ y)) Z); let R0:= framesF w ∘ lotsF YJ
    obtain ⟨hc',h'⟩:= vesper (k:=k) a hp b hg hn z hu hv hl hD he hPt hτ hE f₀ w Z hX hF ht h1 ζ hc hb hM
    change ContDiffAt ℝ n Y 0 at hc'
    have hR:=hp.rehearsed; have hT0:= hp.acts F k; have hP:= hR.tensions; have hx':Nonwrapping X (wrap f b):=short_nonwrap hO hR.weft.cover hp.space hw
    have hspace:100 ≤ f.val:= S.sizes ▸ le_trans (le_trans (Nat.le_mul_of_pos_right 100 (by omega)) hp.space) (Nat.le_mul_of_pos_right _ S.patch.L.property)
    have hW := border_healthy hp.sew C.width C.price hR.early hT0 E.majorant (by omega) hP a hp.bulletin C.Z rfl hR.wire hp.space hR.temp_eq hV U z hu hv R.threshold_pos (q:=q) (d:=d)
    have hs: ‖a.extra g u z‖ ≤ loom P _ _:= (a.extra_size _ _ hu _).trans (hv.trans hP.noise)
    have hL := hP.small.trans (min_le_right ..)
    obtain ⟨hx,hx'₁⟩:= plucked a hp.bulletin hR.weft hT0 hO hg hw C.C_one hP.allows U z hs D E.majorant (by omega) hL hW
    have h0 : Heritage R X b pⁱ w q₀ (Y 0) (Kit.slope S.patch.L) (1+I₀+(1+I₂)):=by
       have hx : Heritage R X b pⁱ w q₀ ((iteratedFDeriv ℝ 0 Y 0) 0) (Kit.slope S.patch.L) _:= h' 0 (Nat.zero_le _) 0 (by simp); rwa [iteratedFDeriv_zero_apply] at hx
    obtain ⟨hQ,hQ'⟩:=boxed1 S.patch.L
    have hZ : ContDiffAt ℝ n R0 (Y 0):= sighted _ _ YJ heV (show Healthy R.threshold X _ from by simpa only [one_smul,Y] using hx'₁ 1 (by simp)) hR.orders
    have hτ:=hh.1
    let A₀:=1+I₀+(1+I₂); have hA0:1≤A₀:= by unfold A₀; linarith
    have hc:Through n (R0 ∘ Y) 0 ((tithy nf I₀ I₂ Vb q₀)*τ*b'^q₀):=by
       refine ⟨hZ.comp _ hc',fun i hi=>?_⟩; have he:=Pipes.central_one Vb hA0 nf q₀
       refine (slots_bound (U:=Y) hc' hZ hi (C:=(n+1:ℝ)*Pipes.central Vb A₀ nf q₀*τ*b'^q₀) (by positivity) (fun s v hv=>?_)).trans_eq ?_
       · exact sedan YJ R X b (Y 0) (pⁱ) w Vb hQ hQ' hA0 χ₀ hm hvF heV hh (Pipes.purse_pos _ _ _ hF) hB hG hS hx' hspace (s.length_le.trans hi) hR.orders hy h0 hx hx'₁ _ (fun j=> h' _ ((s.partSize_le j).trans hi) _ (fun k=>hv _)) hx₀ -- order
       unfold tithy A₀; ring
    have hx:B₀=ᶠ[𝓝 0] R0 ∘ Y:=by
       filter_upwards [depicted (q:=q) (d:=d) a hp.bulletin hR.weft hT0 hO hg hw C.C_one hP.allows U z hs D] with i hi
       change framesF w (changeVars Z (V' _))= framesF w (changeVars _ (YJ (increment 1 _)))
       let g' j:=su.lieExp (V₂ i j); let X:=gauge (g∘ S.ratio.parent) (a.received k T q d u (journey V l D i) U z)
       rw [show YJ (increment 1 (Y i).1)= YJ (gauge g' X) from heV.sites _ _ (agrees_mono hi (fun _ hx=> Finset.mem_union_left _ hx))]; apply congr_arg; change changeVars Z (YJ X)=_; rw [← hG g' X]; exact (AlgHom.congr_fun (change_mul ..) (YJ _)).symm
    exact ⟨hc.smooth.congr_of_eventuallyEq hx,fun i hi=> by rw [(hx.iteratedFDeriv ℝ i).eq_of_nhds]; exact hc.pay i hi⟩
end Fountain
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Fountain.tableau
