import YM.Massive.Reservoir.Cards
/-! # Passing reflection and RG compatibility to limit; path in Arcade -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Cascade
open QCD QCD.Lat Lattice Wilson RG Pressure Gauge Function Filter Set QCD.Tide QCD.Rain QCD.Plum QCD.Agate QCD.Acre QCD.Acre.Rails QCD.Acre.Rails.Reference
open IV QCD.Agate.Supply QCD.Sparks QCD.Land
open MeasureTheory
open scoped Topology Matrix.Norms.L2Operator BigOperators Classical ComplexOrder
variable {n F : ℕ}{J: Patch}{K: KernelChoices}(h:J.Branches K su)(B:SparkMesh)
variable (N p:ℕ→ℕ)(A:∀ i,Run (fixed J K h) (N i) (B.n (p i)) F)
variable (u e :ℕ→ℝ)(v:ℝ)
set_option quotPrecheck false
local notation "S"=> fixed J K h
local notation "s" => fun i m : ℕ=>(fixed J K h).side (B.n (p i)) m
variable {u e v} (ht: Arcade h B N p A u e v)
variable (X:ℕ→ScaleF F)(V W:ℕ→ℝ)(Ω:Ultrafilter ℕ)(hQ:(Ω:Filter ℕ)≤atTop)
local notation "sp"=> sight h B N p A
variable (hz:Glacial h B N p A atTop X V W)
open QCD.Grass
structure Rig (T:ℕ→ScaleF F)(p q:ℕ→ℝ)(B:SparkMesh)(J:Patch)(K:KernelChoices)(e:ℕ→ℝ) :Prop where
    mount(m:ℕ) : p m∈Set.Icc 1 (e m) ∧ q m∈Set.Icc (1/2:ℝ) 2
    dynamics(m:ℕ)(D:Lot)(x:Malt D F) : ∃ y:Malt (rimH D J) F, TrackF J K B (p (m+1)) (q m) m x y ∧ (T m).mass D x=(T (m+1)).mass _ y
    reflection (m:ℕ) : Cer (T m) J
include ht hz
lemma walls (m:ℕ): Cer (X m) J:=by
    constructor; intro Q x D Ω' hm hv hX; apply ge_of_tendsto (hz.cylinders ..); let s':= fun i=> s i m; have hp(i:ℕ):Even (s' i).val:= Even.mul_right (ht.light (p i)) _; have he:= always h B N p A ht m
    filter_upwards [outH Ω' s' he hp _ hX, Agate.trusted Ω' hm x s' he hp,he.eventually (eventually_ge_atTop 4),ht.pace.tendsto_atTop.eventually (eventually_ge_atTop m)] with i h1 h2 h3 h4
    let R:= FaceR Ω' (hp i); have HH : 2 ≤ R.half.val:=by change 4 ≤ (s' i).val at h3; have H:(s' i).val= _:= R.even; omega
    change 0 ≤ Tide.fresh _ _ -- after change wrong
    rw [map_mul,wheeling,← h2]; exact ((A i).state_health (ht.act i) h4).rails R rfl HH _ (palps _ x).hp (palps _ x).hz (staysJ _ _ _ h1)
lemma mount (m:ℕ): V m∈ Set.Icc 1 (e m) ∧ W m∈ Set.Icc (1/2:ℝ) 2 :=
    (isClosed_Icc.prod isClosed_Icc).mem_of_tendsto (hz.sites m) ((ht.pace.tendsto_atTop.eventually (eventually_gt_atTop m)).mono fun i hi=> show _∈ (Set.Icc (1:ℝ) (e m)) ×ˢ Icc (1/2:ℝ) 2 from ⟨ht.base i m hi.le,ht.factor i m hi⟩)
omit hz ht
lemma finesse (i m:ℕ): s i m= finC J B m (p i):= by change B.n _ * _ =_; rw [Reference.ratio h]
-- For comparing fixed scheme implementation with eventual cylinder operation
lemma matchstep {m i:ℕ}{D:Lot}(a w:ℝ)(x:Malt D F)(y:Malt (rimH D J) F)
    (he:Tide.look (Pike J 0) K (powerV B J m (p i)) a w (Agate.visit (origin _) x)=Agate.visit (origin _) y) : Tide.look (Pike J 0) K ((S).sides_next (B.n (p i)) m) a w (Agate.visit (origin _) x)= Agate.visit (origin _) y:=by
     have H (c f:Side)(hf:f=finC J B (m+1) (p i))(hc:c=finC J B m (p i))(hY:f.val=c.val*J.L.val) : Tide.look (Pike J 0) K hY a w (Agate.visit (origin _) x)=Agate.visit (origin _) y:=by subst f c; exact he
     exact H _ _ (finesse h B p i (m+1)) (finesse h B p i m) _
include hz ht
set_option maxHeartbeats 600000 in
lemma dynamic {D:Lot}(m:ℕ)(x:Malt D F): ∃ y:Malt (rimH D J) F, TrackF J K B (V (m+1)) (W m) m x y ∧ (X m).mass D x=(X (m+1)).mass _ y:=by
    have h1:=ht.light 0; have he:=flightH B h1 ht.stamp D m; obtain ⟨k,hk⟩:= he.exists
    let T:=V (m+1); let z:= W m; let f(t q:ℝ):=soared B hk K h t q x; let y:=f T z
    let T₁(i:ℕ):=(A i).β (m+1); let T₂(i:ℕ):=(A i).w m
    let U:= Ultrafilter.of (atTop:Filter ℕ); have hU:(U:Filter ℕ)≤atTop:=Ultrafilter.of_le _
    have hv: 0<z:=(show (0:ℝ)<1/2 from by norm_num).trans_le (Cascade.mount h B N p A ht X V W hz m).2.1
    have hu : Tendsto T₁ (U:Filter ℕ) (𝓝 T):=((continuous_fst.tendsto _).comp (hz.sites (m+1))).mono_left hU
    have hZ : Tendsto T₂ (U:Filter ℕ) (𝓝 z):=((continuous_snd.tendsto _).comp (hz.sites m)).mono_left hU
    obtain ⟨g,hg,hG⟩:= IV.food B U m k hk h x T₁ T₂ T z hu hv.ne' hZ; obtain ⟨r,hr⟩:=encompassed (rimH D J)
    have hy: TrackF J K B T z m x y:= he.mono fun j hj=> flying B h hk hj T z x
    let L:= quota J (2*r+1) v; let H(i:ℕ):= sp x m i - sp y (m+1) i
    have hw:∀ᶠ i:ℕ in atTop, ‖H i‖≤ L*g i:=by
        filter_upwards [ht.pace.tendsto_atTop.eventually (eventually_gt_atTop m),(rises h B N p A ht).eventually he, sights h B N p A ht (m+1) r hr] with j hi hm hL
        let u:=(A j); let X₀:= u.state (m+1); let Y:= f (T₁ j) (T₂ j)
        have hh : sp x m j= sp Y (m+1) j:=by
            have hx:=(A j).active_step (ht.act j) hi
            change Tide.fresh _ _=Tide.fresh _ _; rw [← matchstep h B p (m:=m) (i:=j) (T₁ j) (T₂ j) x Y (flying B h hk hm _ _ x)]; exact Tide.pov (Pike J 0) _ _ _ h ((ht.act j).w_pos hi) hx _ (palps _ x).hp ((A j).standing (ht.act j) hi).1
        change ‖sp x m j- _‖ ≤ _; rw [hh,← sSub h B N p A ht Y y (show m+1≤N j from hi)]; exact (hL _).2 (g j) (hG j)
    have hh:= le_of_tendsto_of_tendsto (( (hz.cylinders m D x).sub (hz.cylinders (m+1) _ y)).norm.mono_left hU) (hg.const_mul L) (hU hw); rw [mul_zero] at hh; exact ⟨y,hy,sub_eq_zero.mp (norm_le_zero_iff.mp hh)⟩
lemma perpetual : Rig X V W B J K e := ⟨Cascade.mount h B N p A ht X V W hz,fun m _ x=> Cascade.dynamic h B N p A ht X V W hz m x,walls h B N p A ht X V W hz⟩ -- D implicit
end YM.Massive.Cascade
#print axioms YM.Massive.Cascade.perpetual
