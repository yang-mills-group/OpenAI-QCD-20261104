import YM.QCD.Quarry.Tavern

/-! # Rooted tests with spin landing. Does not assume common chosen critical chart -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Quarry
open Function Filter Lattice Wilson Lat Stationary Precision RG Tree Tavern Revolve
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff BigOperators
variable {c f n : Side} {S : StepData c f}
abbrev Cnr (n : Side) := Link su n


lemma rot_one (n : Side): siteRot (1:Lat.Frame n)=1:=by unfold siteRot; simp_rw [Pi.one_apply,show colour (1:su.El)=1 from rfl,touch_one]; rw [ridden]
variable (F E:Forest S.ratio)
lemma boot_print (k : Joint su c f) : Stationary.boots S F k ∘ S.ratio.embed=k.2:=by
  funext i; unfold Stationary.boots; simp [Function.comp_apply,Forest.fold_root,Ratio.embed_parent]

abbrev Rooted (S : StepData c f) (A : Grid f→Sheet c) := ∀ (b: Lat.Frame f) U,A (Lattice.gauge b U)=aura (siteRot (b ∘ S.ratio.embed)) (A U)
def mirage (A: Grid f→Sheet c) (ρ : Bid.Dir su c→AxisChart su F) (x : Cnr c):= A (encamp F ρ x).1
variable {F E} {p : Clip} {R : PathData su} {μ δ B D : ℝ} {ρ : Bid.Dir su c→AxisChart su F} {σ : Bid.Dir su c→AxisChart su E}
    (h : Critical F p R ρ) (t:S.Choices) (he : S.patch.Branches S.kernel su) (hR : R.Bounds p δ B D)
    (hk : PriceGap F p R μ) (hm : 0<μ) {A : Grid f→Sheet c} (hu : Rooted S A)
include h t he hR hk hm hu
lemma shelled {X: Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [CompleteSpace X]
    {U : X→Joint su c f} {b : X→Cnr c} (hv : Thaw U 0) (hg : U 0=1) (hz : b 0=0) (hx : ContDiffAt ℝ ω b 0)
    (hy : ∀ᶠ x in 𝓝 0, Shell S t p R (input su c (b x)) (U x)) :
    ∀ᶠ x in 𝓝 0,mirage F A ρ (b x)=aura (siteRot (U x).2) (A (U x).1):=by
  filter_upwards [veterans h he hR hk hm t hv hg hx hz hy] with z H
  rw [mirage,← H, cloak, wages]; dsimp only; rw [hu,boot_print]
lemma panorama (hp : Critical E p R σ):mirage F A ρ=ᶠ[𝓝 0] mirage E A σ:=by
  filter_upwards [shelled h t he hR hk hm hu (U:=encamp E σ) (b:=id) (camp_thaw hp) (encamp_zero hp) rfl contDiffAt_id (camp_station hp he hR t)] with x H
  rw [id_eq] at H; rw [H]; change aura (siteRot (1:Lat.Frame c)) _=_; rw [rot_one,aura,star_one,one_mul,mul_one]; rfl
lemma static (k:su.El):
    ∀ᶠ x in 𝓝 0,mirage F A ρ (stain k x)= aura (siteRot fun _=>k) (mirage F A ρ x):=by
  let b:= stain (m:=c) k; let V := encamp F ρ
  let j : Lat.Frame f:=fun _=>k
  let k' : Lat.Frame c:=fun _=>k
  let U x:= wages S j k' (V x)
  have hx : U 0=1:=by ext i <;> simp [U,V,wages,k',j,Lattice.gauge, encamp_zero h]
  have heq (x:Cnr c):Lattice.gauge k' (input su c x)=input su c (b x):=stain_cons k x
  have H : ∀ᶠ x in 𝓝 0, Shell S t p R (input su c (b x)) (U x):= (camp_station h he hR t).mono (fun x hd=> heq x ▸ hd.wage he hR j k')
  have ht:Thaw U 0:=(camp_thaw h).wages S (Army.park _ _) (Army.park _ _)
  filter_upwards [shelled h t he hR hk hm hu ht hx (map_zero b) b.contDiff.contDiffAt H] with x hh
  have hr (x:Cnr c) : (U x).2=1:= by funext i; simp [U,V,wages,j,k',encamp,abode]
  change mirage F A ρ (b x)=_
  rw [hh,hr,rot_one, aura,star_one,one_mul,mul_one]; exact hu j _
lemma trek : ∀ᶠ x : Swatch su c in 𝓝 0, mirage F A ρ (moveField x)=aura (siteRot (switchSite x.1)) (mirage F A ρ x.2):=by
  let U (x:Swatch su c):= wages S 1 (switchSite x.1) (encamp F ρ x.2)
  have hx : U 0=1:= (show _ from by simp only [U,Prod.fst_zero,Prod.snd_zero,switch_zero,wages_zero]; exact encamp_zero h)
  have hp : Thaw U 0:= ((Thaw.comp (x:=(0:Swatch su c)) (g:=encamp F ρ) (w:=Prod.snd) (camp_thaw h) contDiffAt_snd)).wages S (Army.park _ _) (Army.powG (v:=Prod.fst) contDiffAt_fst)
  have hy : ∀ᶠ x : Swatch su c in 𝓝 0, Shell S t p R (input su c (moveField x)) (U x):=by
    filter_upwards [moveField_germ (G:=su) (m:=c),(continuous_snd.tendsto (0:Swatch su c)).eventually (camp_station h he hR t)] with x hz hu; rw [hz]; exact hu.wage he hR 1 _
  filter_upwards [shelled h t he hR hk hm hu hp hx moveField_zero moveField_analytic.contDiffAt hy] with x ht
  rw [ht]; have HH : (U x).2=switchSite x.1:=by funext; simp [U,wages,encamp,abode]
  have ha: (U x).1=(encamp F ρ x.2).1:= gauge_one _
  rw [HH,ha]; rfl
lemma orbit_space (b : Site c)(l : Site c→ℂ)(hp : ∀ U,A (pull 1 (S.ratio.embed b) U)= aura (hues b 1 l 1) (A U)):
    ∀ᶠ x : Cnr c in 𝓝 0, mirage F A ρ (spaceShift b x)=aura (hues b 1 l 1) (mirage F A ρ x) := by
  let U := road S b ∘ (encamp F ρ)
  have hx : U 0=1:=by unfold U; rw [Function.comp_apply,encamp_zero h,road1]
  have hg := road_diff S b (camp_thaw h)
  have hs : ∀ᶠ x in 𝓝 0, Shell S t p R (input su c (spaceShift b x)) (U x):=by
    filter_upwards [camp_station h he hR (S.withinChoice 1 b t)] with x H; rw [input_run]; exact updated S b _ _ _ _ _ he H
  filter_upwards [shelled h t he hR hk hm hu hg hx (map_zero _) (spaceShift b).contDiff.contDiffAt hs] with x H
  rw [H,show (U x).2=1 from rfl, rot_one,aura,star_one,one_mul,mul_one]; exact hp (encamp F ρ x).1
lemma orbit_compass (s : Signed)(l : Site c→ℂ)(P : Spike)(hp : ∀ U,A (pull s 0 U)= aura (hues 0 s l P) (A U)):
    ∀ᶠ x : Cnr c in 𝓝 0, mirage F A ρ (orderTurn s x)=aura (hues 0 s l P) (mirage F A ρ x) := by
  let U x:= twistUniform s (encamp F ρ x)
  have hx : U 0=1:=by unfold U; rw [encamp_zero h,twistUniform_one]
  have hg := stationed_twist s (camp_thaw h)
  have hs : ∀ᶠ x in 𝓝 0,Shell S t p R (input su c (orderTurn s x)) (U x):=by
    filter_upwards [camp_station h he hR (S.withinChoice s 0 t)] with x H; erw [← flip_links s x]; exact sail s t he _ _ H
  filter_upwards [shelled h t he hR hk hm hu hg hx (map_zero _) (orderTurn s).contDiff.contDiffAt hs] with x H
  rw [H,show (U x).2=1 from rfl, rot_one,aura,star_one,one_mul,mul_one]; exact hp (encamp F ρ x).1
end YM.QCD.Quarry
