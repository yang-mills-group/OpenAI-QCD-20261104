import YM.Massive.Filament.Felt
/-! # Coherent Strut and gauge, phases and reality through K stack on thermal remap.

Adapted from `QCD/Ruby/Rows`. Everything still in μ-fixed radius Cauchy, so needed real λ evaluations only.
Permutations `Plot` must not be reselected at each V or at each phase. Supports preserved
on real ζ even for common η origin. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fibre
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open Massive.Filament Ruby Fused
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N B:ℕ}{h A R C D W r:ℝ}{s z:ℂ} {ι α: Type}
local notation "Q"=> EvenA c N
local notation "D!"=> Grid c
variable (Y: ℂ→ℂ→ Ruby.Hue c N α)(X: ℂ → ℂ → Rail c N ι)
-- fields.B.value. Bud economics kept externally.
def Swung (p: Strut c) (k: Spike) (g:Site c→ℂ)(w:Equiv.Perm α)(X:Ruby.Hue c N α):Prop:=∀ i, (X.bud (w i)=(X.bud i).image (act p))∧∀ U:Grid c, Diode N p k g (X.mean i (sky p U))=X.mean (w i) U
structure Theme (X: ℂ→ Ruby.Hue c N α) : Prop where
 life (z:ℝ) (i:α): ‖z‖< (1:ℝ) → Grit ((X z).mean i)
 trueShift (p:Strut c)(k:Spike)(g: Site c→ℂ): Warrant p g k→∃ w:Equiv.Perm α,∀ z:ℝ, ‖z‖<1→Swung p k g w (X z)
lemma themeG (Z: Ruby.Hue c N α)(hp:Z.Garish): Theme (fun _=>Z):=by refine ⟨fun z i _=>⟨hp.gauge i,fun U=>Pith.fitP _ (hp.number i U),fun U=>hp.real i U⟩,?_⟩; intro s k g h; obtain ⟨w,hp,he⟩:= hp.travel s k g h; exact ⟨w,fun _ _ i=> ⟨hp i,he i⟩⟩
lemma orbit (Y:Ruby.Hue c N α)(X:Rail c N ι)(t:ℝ) (hY:∀ i,Grit (Y.mean i)) (hX:∀ i,Grit (X.warp i))(v:Plot Y X): Grit ((Trail Y X t).warp v):=by
   let M:=Trail Y X t
   have he (K:EvenA c N →+* EvenA c N)(hk':Continuous K) (V U:Grid c)(hf:RG.flags t V=RG.flags t U) (H:∀ i,K (Y.mean i V)= Y.mean i U)(hC:∀ i,K (X.warp i V)= X.warp i U)(i:Plot Y X): K (M.warp i V)= M.warp i U:=by
      have hk : Got (oriD X) (Equiv.refl _) (Equiv.refl _):=by intro; simp
      have hx: Got (Ruby.home X) (Equiv.refl _) (Equiv.refl _):=by intro; simp
      have hp': Got Y.bud (Equiv.refl _) (Equiv.refl _):=by intro; simp
      have hx:=phones Y X (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) hk hx hp' hk' (Finset.image_id.trans hf) H hC i.val; rw [show (Equiv.sumCongr (Equiv.refl _) (Equiv.refl _)).finsetCongr i.val=i.val from (by simp)] at hx; exact hx
   refine ⟨fun V k=>congr_arg Subtype.val (he (trade (Lat.rotates N k)).passL (phare _) (gauge k V) V (gauge_flags ..) (fun i=> Subtype.ext ((hY i).gauge V k)) (fun i=>Subtype.ext ((hX i).gauge V k)) v), fun U w hw=> he (trade (flute (Lat.Row c) (Matrix.diagonal w))).passL (phare _) U U rfl (fun i=> (hY i).flex U w hw) (fun i=>(hX i).flex U w hw) v, fun U=> he (Regal c N) (phare _) U U rfl (fun i=> (hY i).real U) (fun i => (hX i).real U) v⟩
local notation "X₀"=> X 0 0
local notation "Y₀"=> Y 0 0
variable {Y X}
variable (hP:Arc X)(hp:Arch Y)
include hP hp
-- parametric: build π across *any* shape of the firm's directions. Marker S doesn't currently matter. change to polynomial family later for E expressions.
lemma Theme.trail (hX: MatchX (fun z=> X z s))(hY:Theme (fun z=> Y z s)) (t:ℝ): MatchX (fun z=> glen X Y z s t):=by
   constructor
   · intro z i hz; refine orbit (welded Y z s) (loose X z s) _ (fun i=>?_ ) (fun j=> ?_) i
     · rw [hp.equal]; exact hY.life z i hz
     rw [hP.equal]; exact hX.life z j hz
   intro p k g hx; obtain ⟨w,h⟩:= hX.trueShift p k g hx; obtain ⟨q,hq⟩:= hY.trueShift p k g hx
   have hF (z:ℝ)(hz:‖z‖<1): Swing p k g w (loose X z s) ∧ Swung p k g q (welded Y z s):=by rw [hp.equal,hP.equal]; exact ⟨h _ hz,hq _ hz⟩
   obtain ⟨hR,hA⟩:= hF 0 (by simp); let v:=act p; have hj:Got (oriD X₀) w v:= fun i=> (hR i).2.1; have hk: Got (Ruby.home X₀) w v:=fun i=>(hR i).1; have h1: Got (Y₀).bud q v:=fun i=> (hA i).1
   let W:=Equiv.subtypeEquiv (Equiv.sumCongr w q).finsetCongr (jewels Y₀ X₀ v q w hj hk h1)
   refine ⟨W,fun z hz i=>?_⟩; obtain ⟨he,hb⟩:= hF z hz; exact ⟨wingP Y₀ X₀ v q w hk h1 _,ocean X₀ v q w hj _, fun V=> phones (welded Y z s) (loose X z s) v q w hj hk h1 (phare _) (Work.H03.flags_send ..) (fun j=> (hb j).2 V) (fun j=>(he j).2.2 V) _⟩
omit hP hp
lemma colors (X: Grid c→ Q) (h:Grit X)(t:ℝ): Grit (fun U=>wearK c N t (X U)):=by
   refine ⟨fun V z=>?_, fun X' i hi=> (purity _ _ t).trans (congr_arg _ (h.flex X' i hi)), fun U=>(dearR _ t).trans (congr_arg _ (h.real U))⟩
   let K:=Lat.rotates N z; exact congr_arg Subtype.val ((purity K (X (gauge z V)) t).trans (congr_arg (wearK c N t) (show sways K (X (gauge z V))=X V from Subtype.ext (h.gauge V z))))
lemma MatchX.rises (X:ℂ→Rail c N ι)(t:ℝ)(H:MatchX X): MatchX (fun z=> flightK (X z) t):=by
     refine ⟨fun z i hz=>colors _ (H.life z i hz) t,?_⟩; intro p k g hg; obtain ⟨w,hw⟩:= H.trueShift p k g hg; refine ⟨w,fun z hz i=>?_⟩; obtain ⟨hf,hg,hr⟩:= hw z hz i; exact ⟨hf,hg,fun U=> (purity _ _ _).trans (congr_arg (wearK c N t) (hr U))⟩
-- The boost estimates use Arc everywhere + MatchX. for warmth after first merge Reg still needs separate.
lemma rateK (X:Rail c N ι)(h:X.Reg A)(t:ℝ): (flightK X t).Reg A:= by
   refine ⟨fun i U V hz hq=>congr_arg (wearK c N t) (h.uses i U V hz hq),fun i=> (songT (c:=c) (N:=N) t).continuous.measurable.comp (h.reads i), fun i U=> dings t _ _ (h.role ..), fun i U hx=> h.buys i U (fun hw=>hx ((congr_arg _ hw).trans (map_zero (wearK c N t))))⟩
end YM.QCD.Fibre
#print axioms YM.QCD.Fibre.Theme.trail
