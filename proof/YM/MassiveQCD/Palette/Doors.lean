import YM.MassiveQCD.Palette.Symmetry
import YM.QCD.Ruby.Full
/-! # Soft-log connector to hard ticket occurrences only -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}
-- Soft credits equivalent compressed weighted quota
structure Hue.Doorways (Y:Hue c N ι) :Prop where
  gauge i: shadeG (Y.mean i)
  real i U: Regal c N (Y.mean i U)=Y.mean i U
  number i U : AccentFit (Y.mean i U)
  travel s k g: Warrant s g k→∃ e, Got Y.bud e (act s)∧∀ (i:ι) (U: Grid c), Diode N s k g (Y.mean i (sky s U))=Y.mean (e i) U -- change forall

variable (Y:Hue c N ι) (X:Rail c N β){ρ:Type}
lemma track_color (pY:Y.Doorways) (hp:MixedInk X) (t:ℝ): MixedInk (Trail Y X t):=by
   have hk : Got (oriD X) (Equiv.refl _) (Equiv.refl _):=by intro; simp
   have hx: Got (home X) (Equiv.refl _) (Equiv.refl _):=by intro; simp
   have hp': Got Y.bud (Equiv.refl _) (Equiv.refl _):=by intro; simp
   let M:=Trail Y X t
   have he (K:EvenA c N →+* EvenA c N)(hk':Continuous K) (V U:Grid c)(hf:RG.flags t V=RG.flags t U) (H:∀ i,K (Y.mean i V)= Y.mean i U)(hC:∀ i,K (X.warp i V)= X.warp i U)(i:Plot Y X): K (M.warp i V)= M.warp i U:=by
      have hx:=phones Y X (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) hk hx hp' hk' (Finset.image_id.trans hf) H hC i.val; rw [show (Equiv.sumCongr (Equiv.refl _) (Equiv.refl _)).finsetCongr i.val=i.val from (by simp)] at hx; exact hx
   constructor
   · intro i V k; exact congr_arg Subtype.val (he (trade (Lat.rotates N k)).passL (phare _) (gauge k V) V (gauge_flags ..) (fun i=> Subtype.ext (pY.gauge i V k)) (fun i=>Subtype.ext (hp.gauge i V k)) i)
   · intro i V W hW; exact he (trade (flute (Lat.Row c) W)).passL (phare _) V V rfl (fun i=>pY.number i V W hW) (fun i=> hp.num i V W hW) i -- order num before real
   · exact fun i V=> he (dawn (idol c N)).passL (phare _) V V rfl (fun i=>pY.real i V) (fun i=>hp.real i V) i
   intro s z k h; obtain ⟨p,h1,h2⟩:= pY.travel s k z h; obtain ⟨q,hq⟩:=hp.moves s z k h
   let x:= act s; have hP: Got (home X) q x:=fun i=> (hq i).1; have hT: Got (oriD X) q x:=fun i=> (hq i).2.1
   refine ⟨Equiv.subtypeEquiv (Equiv.sumCongr q p).finsetCongr (jewels Y X x p q hT hP h1),fun i=>?_⟩
   exact ⟨wingP Y X x p q hP h1 _,ocean X x p q hT _, fun V=> phones Y X x p q hT hP h1 (phare _) (Work.H03.flags_send ..) (fun i=> h2 i _) (fun i=> (hq i).2.2 V) _⟩

lemma track_sum (Z:Hue c N ρ)(hh:Y.Doorways)(he:Z.Doorways): (HJoin Y Z).Doorways:=by
    refine ⟨?_,?_,?_,?_⟩
    · rintro (i|i); exact hh.gauge i; exact he.gauge i
    · rintro (i|i); exact hh.real i; exact he.real i
    · rintro (i|i); exact hh.number i; exact he.number i
    intro s k g h; obtain ⟨d,hf,hv⟩:= hh.travel _ _ _ h; obtain ⟨f,hF,hX⟩:= he.travel _ _ _ h
    exact ⟨Equiv.sumCongr d f, (fun i=> by rcases i with i|i; exact hf i; exact hF i), fun i U=> by rcases i with i|i; exact hv i _; exact hX i _⟩
lemma track_average (hh:∀ i,shadeG (Y.mean i))(ht:∀ i U,AccentFit (Y.mean i U))(he:∀ i U,Regal _ _ (Y.mean i U)=Y.mean i U): (HGrace Y).Doorways:=by
    constructor
    · rintro ⟨v,i⟩ U k
      suffices he : sways (Lat.rotates N k) ((HGrace Y).mean (v,i) (gauge k U))=(HGrace Y).mean (v,i) U by exact congr_arg Subtype.val he
      let P:= spice v (N:=N); change sways _ (averageC c • _) = averageC c • _; rw [eSM _ (phare _),show sky v (gauge k U)=gauge (k ∘ act v) (sky v U) from pull_gauge ..]; apply congr_arg; unfold spice
      rw [custodial k _ (assured v)]; apply congr_arg; exact Subtype.ext (hh i (sky v U) (k ∘ act v))
    · rintro ⟨s,i⟩ U; apply Patron.dolled; exact (AccentFit.gammaT _ (ht i _) (assured s)).trans (congr_arg _ (he i _))
    · rintro ⟨s,i⟩ U; exact AccentFit.dated _ _ (AccentFit.polarizei _ (ht i _) _)
    intro s k g h; refine ⟨Equiv.prodCongr (skyEquiv s) (Equiv.refl _),?_,?_⟩
    · rintro ⟨p,i⟩; change (Y.bud i).image (act (pod s p))=((Y.bud i).image (act p)).image (act s); rw [podA,image_image]; rfl
    rintro ⟨p,i⟩ U; change Diode N s k g (averageC c • spice p (Y.mean i (sky p (sky s U))))= averageC c • spice (pod s p) (Y.mean i (sky (pod s p) U)); rw [skying,eSM _ (phare _)]; apply congr_arg; change sways _ (sways _ _)=_; rw [leaps,← copies_mul,← beset _ _ _ _ g (ink p)]; exact AccentFit.coinT (Y.mean i _) (ht i _) (Strut.comb h (assured p)) (assured _)

lemma track_gauge (hp:∀ i, shadeG (X.warp i)) (h:∀ i, shadeG (Y.mean i))(s:ℝ)(i:Plot Y X): shadeG ((Trail Y X s).warp i):=by -- complex
    have hk : Got (oriD X) (Equiv.refl _) (Equiv.refl _):=by intro; simp
    have hx: Got (home X) (Equiv.refl _) (Equiv.refl _):=by intro; simp
    have hp': Got Y.bud (Equiv.refl _) (Equiv.refl _):=by intro; simp
    intro U k; let M:= trade (Lat.rotates N k); have hz:=phones Y X (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) hk hx hp' (phare M) (Finset.image_id.trans (gauge_flags s U k)) (fun i=>Subtype.ext (h i U k)) (fun i=>Subtype.ext (hp i U k)) i.val
    rw [show (Equiv.sumCongr (Equiv.refl _) (Equiv.refl _)).finsetCongr i.val=i.val from (by simp)] at hz; exact congr_arg Subtype.val hz
end YM.QCD.Ruby
