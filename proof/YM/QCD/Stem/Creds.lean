import YM.QCD.Stem.Chiasm
/-! # lift end credits as pigments. Includes χ unmask and potter none. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stem
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure Precision ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove AnalyticBridge VerifiedReset
variable {C:Side}{D D' w j:ℕ}{d r t t' p p' η b z A:ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove YM.Next.Scheduling Footprint Moss Extra.Iteration
section cred
structure TokenB (E:Ruby.Hue c N I) (h:ℝ)(W:ℕ)(t d p:ℝ):Prop where
   mask : E.Tall h
   gauge i: shadeG (E.mean i)
   fit i V: Fit (E.mean i V)
   real i V: Regal c N (E.mean i V)=E.mean i V
   pay : ∃ f:I→ℝ,Ac.Hit E.bud W f t d ∧∀ i U, ‖token c N p (E.mean i U)‖≤ f i
-- for sunny receipts use all χ.Tall. rehab
variable (G:Gem c N I)(h:Licence B t d p G)(ht:Dyed G)(hk:0 < p)
lemma tipped (f:I→ℝ)(X:Anchored (fun i=>(G.addr i).site) f (fun i=>coverNumber w (G.addr i).support) r t)(he:∀ i,0≤f i)(hv:t'+1+1≤r)(hh:0≤t') : Ac.Hit (fun i=>(G.addr i).support) w f t' (payment 1 (4*w+2) 0 1 1 t t' 0):=by
   apply Footprint.assigned id 1 (fun Y=> by simp) (fun i=>(G.addr i).site) _ he _ _ X _ _ _ (fun i x p=> ?_) (v':=1) (fun i=> by simp) zero_le_one ⟨hh,zero_lt_one,by linarith⟩ f he (by simp)
   exact (Corona.extent (G.addr i).support w p (G.addr i).anchor).trans (by nlinarith ) -- dummy
noncomputable def hoist (G:Gem c N I)(t:ℝ): Ruby.Hue c N I:=⟨fun i=>(G.addr i).support, fun i V=> G.view i V-letters G t V i⟩
local notation "H₁"=> hoist G B.threshold
-- hT, unmasked peg bound
include h ht hk
lemma stony (f:I→ℝ)(hπ:Anchored (fun i=>(G.addr i).site) f (fun i=>coverNumber B.B (G.addr i).support) r A)(hp:∀ i V,‖token c N p (G.view i V)‖ ≤ f i)(hr:t'+1+1≤r)(he:0≤ t') : TokenB H₁ B.threshold B.B t' (payment 1 (4*B.B+2) 0 1 1 A t' 0) p:=by
   obtain ⟨u,hv,h⟩:=h.zone; have hh i:= wonders (G.view i) (G.addr i).support B.threshold (ht.gauge i) (ht.num i) (ht.real i) (h i).gated
   have hg i V (a:Healthy B.threshold (G.addr i).support V): (H₁).mean i V=0:= sub_eq_zero.mpr (masked_eq _ _ _ _ a).symm
   have hf i: 0≤ f i:=(norm_nonneg _).trans (hp i 1)
   refine ⟨⟨fun i U V a b=> congr_arg₂ (·-·) ?_ (clearUse G i (h i).room B.threshold U V a b), fun i=> ((h i).Borel).sub (RG.masked_measurable _ _ _ (h i).Borel),fun i V a k=> a (hg _ _ k),fun i V=> wingsZ _ _ _ ((h i).gated _) ((hh i).2 _|>.2.2)⟩,fun i U k=> congr_arg Subtype.val (show sways (Lat.rotates N k) (_-_)=(H₁).mean i U from ?_),fun i V W hv=> ?_,fun i V=>?_,f,tipped G f hπ hf hr he, fun i V=> ?_⟩
   · exact (h i).room U V a
   · rw [map_sub]; exact congr_arg₂ (·-·) (show sways (Lat.rotates N k) _=G.view i U from Subtype.ext (ht.gauge i U k)) (Subtype.ext ((hh i).1 U k))
   · change sways _ (_-_)=_; rw [map_sub,ht.num i V W hv]; exact congr_arg₂ (·-·) rfl (((hh i).2 V).1 W hv)
   · change Regal c N (_-_)=_; rw [map_sub,ht.real]; exact congr_arg₂ (·-·) rfl ((hh i).2 V|>.2.1)
   by_cases hz: Healthy B.threshold (G.addr i).support V; · rw [hg i V hz,map_zero,norm_zero]; exact hf i
   change ‖token _ _ _ (_-letters _ _ _ _)‖≤_; unfold letters; rw [masked_ne _ _ _ _ hz,sub_zero]; exact hp i V
omit h ht hk
variable (T:ℕ→ Atom su j)(V:Grid c)
open Song Quotes
abbrev heftL (T:ℕ→ Atom su j)(b:ℝ)(i:ℕ):ℝ:=|VerifiedReset.factor*(-b)| *2^j*(T i).magnitude
lemma tollT (i:Stave (n:=c))(hr:0≤p): Sen ((codaX T N b c).addr i).site p ((codaX T N b c).view i V) ≤ heftL T b i.2:=by
   unfold codaX; simp only [Function.comp_apply, vintage _ _ _ hr, tuneAtom,Pi.smul_apply,norm_smul]; unfold heftL; rw [mul_assoc]; change _ ≤ ‖(VerifiedReset.factor*(-b))‖ *_; exact mul_le_mul_of_nonneg_left ((T i.2).unmasked_bound .. |>.trans_eq (mul_comm ..)) (norm_nonneg _)
lemma megaT (h : Charged T t d)(hp : 0<t)(he: preExponent B/B.B≤t) : Quotes.early B (pitch (n:=c) T) (fun i=> heftL T b i.2) (anchoredFee (Song.headline B) (Song.octave j)*(|VerifiedReset.factor*(-b)| *2^j*d)):=by
   apply enhanced; let D:= |VerifiedReset.factor*(-b)| *2^j; have hd:0≤D:=by unfold D; positivity; -- edit indentation
   refine Quotes.channel_mass (p:=Song.headline B) (fun i=> (T i).length) (fun i=>(T i).footprint (0:Site c)) (heftL T b) (fun i=>mul_nonneg hd (by unfold Atom.magnitude; positivity)) (σ:=t+t) ?_ (Song.octave j) (show preExponent B/B.B≤ _ from he.trans (by linarith)) ?_
   · convert Extra.Iteration.Cost.scale h D hd using 2 with i; rw [show (t+t)/2=t by ring]; unfold heftL Atom.budget D; ring
   intro i; have ht:= Wages.traversed (T i) (0:Site c) B.B B.B_pos; change B.B*_ ≤ B.B*Song.octave j+_; simp only [Song.octave,Song.headline]; nlinarith -- shape
end cred
end YM.QCD.Stem
