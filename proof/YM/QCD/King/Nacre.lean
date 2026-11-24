import YM.QCD.King.Loom
/-! # Branch Meter from physical stencil. Hard plateau (not dividing real mask) -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.King
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Golden
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open Push.AbsoluteSums Mixed Trees Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (Ξ : Utopia H j v η r C' χ)
set_option quotPrecheck false
open Pipe
variable {w':ι→ℝ}{g:ℝ→ℝ}{x' Ω Λ t u pu θ e:ℝ}{i m:ℕ}
-- cap an exponential with zero. Full mark column.
def Cargo (U:Coat T F)(a:ℝ)(z:Directions su f)(I: Support c):Prop:=∀ i∈U.plaza I, ‖z i‖ ≤ 2*a*U.t
lemma drapeG (p:Woods P L (2*a) g x') (V:Support c)(U:Coat T F)(i:Site c)(w:Directions su f)(hw:Cargo U (2*a) w V) (hx:U.x=x')(hL:S.patch.L=L)(hp:Room P S T U.x)(ht:U.manifest)(hh:halo (6*radiusB x') {i}⊆V)(hz:¬Inside i U.seeds (18*radiusB x'))(hF:0<a):∃ A b, Blanket S (U.input w) U.V i (4*radiusB x') A b (g x'):=by
    refine p.cloth U hx hL (hx ▸ hp) ht V i w hh ?_ hz; unfold Coat.enforce; rw [show (∏ x∈U.plaza V,U.cone (2*(2*a)) w x)=1 from ?_]; exact one_ne_zero
    have hf: 0<U.t:= hp.fiery; exact Finset.prod_eq_one fun i hi=> U.premiere (by positivity) w i (hw i hi)
-- Gap motion: actual inner mask along shifted Y
lemma filterW (k': Kite Ξ A b Ω n pu k θ)(h:Y.Famous)(U:Coat T F)(i:ι)(z:Air f su) {W':E→Directions su f}
 (hh:U.x=s)(hm:U.manifest)(hz:U.width=o.K)(hu:U.χ=χ)(hp:Mode V x j v)(hw:Clutch U z o.a R.beta η x j V W' (fun t=>course U A R.beta z (V t)))(f:ℝ):
 let Z:=worldZ U R.beta z; let F' v:=steer U A Z (V v); let M y:= U.enforce (2*o.a) (F' y) (U.plaza (Y.window i));
 (warm Y U z i V A f x=ᶠ[𝓝 x] fun y=> M y • songT (N:=N) f (Y.works i (U.input Z) (V y))) ∧ Brush j 1 (windy Y θ i) M x ∧ (¬Cargo U (2*o.a) Z (Y.window i) → M =ᶠ[𝓝 x] 0) :=by
   intro Z F' M
   have h₁ := k'.flow F U hh hu hz hm _ V x hw.atV hp
   obtain ⟨hZ,hF,hC⟩:=h₁.2 z
   have hFu:0<o.a*U.t:= hZ.pulse
   refine ⟨?_,?_,?_⟩
   · filter_upwards [nearby U k'.cap hw.atV hp] with y hy; unfold warm; rw [(pulp Y h k'.cap U z i (V y) hy hFu (_:8*o.a*U.t≤A/2)).1]
     exact map_smul (songT (c:=c) (N:=N) f) _ (Y.works i _ _)
     unfold Coat.t; rw [hh,H.laws.data.funds.length_eq]; exact k'.speed
   · unfold windy
     have hx:(U.B=radiusB s):= congr_arg _ hh
     rw [← hx]; exact hC (Y.window i) (Y.ground i) ((halo_subset _ _).trans (h.boot i))
   intro h; unfold Cargo at h; push Not at h; obtain ⟨m,hm,h⟩:=h
   have he:F' x=Z:= by change steer _ _ _ _=_; rw [hw.atV]; funext i; unfold steer Silica.action; simp [Eider.nothing_f k'.cap]
   have hp:ContinuousAt (fun y=>‖F' y m‖) x:=by
       let f' y:= F' y m; let g y:= f' y-Z m
       have he' : f'=(fun y=> g y+ Z m):=by funext y; unfold g; abel
       have hb:ContinuousAt f' x:= he'.symm ▸ (show ContinuousAt (fun y=>g y+Z m) x from (hZ.bud m).smooth.continuousAt.add continuousAt_const)
       exact hb.norm
   filter_upwards [hp.eventually (lt_mem_nhds (show 2*(2*o.a)*U.t< ‖F' x m‖ from he.symm ▸ h))] with y hy
   unfold M Coat.enforce; exact prod_eq_zero hm (by_contra fun hv=> (show 2*(2*o.a)*U.t<‖F' y m‖ from hy).not_ge (U.amount (by rw [mul_assoc]; positivity) (F' y) m hv))
structure Honest (A:ℝ)(Λ t:ℝ)(w:ι→ℝ)(e v:ℝ)(χ:Chi)(j:ℕ)(P:ι→Site c)(Z: Finset ι)(k n:ℕ):Prop where
 cost:∀ i,0≤w i
 yPos:0≤ Λ
 age:0 ≤ t
 home :∀ (F:Forest S.ratio)(U:Coat T F),U.width=o.K → U.manifest → U.x=s → U.χ=χ → ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](x:E)(V:E → Config su c)(z:Air f su), V x=U.V → Mode V x j v → ∀ i, Cargo U (2*o.a) (worldZ U R.beta z) (Y.window i) →
   let M y:= wearK c N e (Y.works i (U.input (worldZ U R.beta z)) (V y))
   (Brush j (w i) (windy Y Λ i) M x ∨ i∈ Z ∧ ∃ u∈ Y.ground i,u∈ U.seeds.place ∧ separation u (P i) ≤ k)∧ Brush j (Real.exp t*w i) (windy Y Λ i) M x
 cover :∀ y,(Z.filter fun j=> P j=y).card≤n
lemma induced {P:ι→Site c}{s':Finset ι}(p:Kite Ξ A b Ω n pu k θ) (h:Y.Famous)(hp:Honest Y A Λ t w' e v χ j P s' i m): Enters Y r A (θ+Λ) t w' e v η χ j P s' i m:=by
    refine ⟨add_nonneg p.earns hp.yPos,hp.age,hp.cost,?_,hp.cover⟩
    intro F U ht hh he hy E _ _ _ x V W z hV hx rho
    let M i:= wearK c N e (Y.works rho (U.input (worldZ U R.beta z)) (V i)); let q:= windy Y (θ+Λ) rho
    obtain ⟨hS,hie,hZ⟩:= filterW Y Ξ p h U rho z he hh ht hy hV hx e
    have hcom : q=windy Y θ rho+windy Y Λ rho:=add_mul ..
    have hr :0≤q:= mul_nonneg (add_nonneg p.earns hp.yPos) (Nat.cast_nonneg _)
    by_cases ht':Cargo U (2*o.a) (worldZ U R.beta z) (Y.window rho)
    · obtain ⟨hp',hv⟩:=hp.home F U ht hh he hy _ x V z hx.atV hV rho ht'
      have he a (hg:Brush j a (windy Y Λ rho) M x): Brush j a q (warm Y U z rho V A e x) x:=by
          have hh := (brushR hie hg).shimmy hS; rw [one_mul] at hh; exact hcom.symm ▸ hh
      exact ⟨hp'.imp_left (he _),he _ hv⟩
    have hh:(warm Y U z rho V A e x)=ᶠ[𝓝 x]0:=by filter_upwards [hS,hZ ht'] with i hi hv; exact hi.trans (congr_arg₂ (fun (a:ℝ)(b:EvenA c N)=>a • b) (show U.enforce _ _ _=0 from hv) rfl|>.trans (zero_smul ..))
    exact ⟨Or.inl (Brush.zi hh (hp.cost _) hr), Brush.zi hh (mul_nonneg (Real.exp_pos _).le (hp.cost _)) hr⟩
end YM.ConnectedActivityE6.Blaze.King
