import YM.QCD.Ruby.Tickets
/-! # covariance refund -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Trees
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}{a u v w A R m k σ B' v' ht q':ℝ} {B:ℕ}
variable (Y:Hue c N ι) (X:Rail c N β)
variable {K:EvenA c N→+*EvenA c N}
variable {U V:Grid c} (x:Equiv.Perm (Site c))(p:Equiv.Perm ι)(q:Equiv.Perm β)
variable (hj:Got (oriD X) q x)(hk:Got (home X) q x) (hY: Got Y.bud p x)
local notation "E" => Equiv.sumCongr q p
lemma outfits (i:Cart ι β): ((E).finsetCongr i).toLeft=q.finsetCongr i.toLeft ∧ ((E).finsetCongr i).toRight=p.finsetCongr i.toRight:=by
    constructor
    · ext j; obtain ⟨j,rfl⟩:=q.surjective j; simp
    ext j; obtain ⟨j,rfl⟩:=p.surjective j; simp
include hk hY
lemma gold : Got (footD Y X) (E) x:=by rintro (i|i); exact hk i; exact hY i
lemma wingP (s:Cart ι β): scopeK Y X ((E).finsetCongr s)=(scopeK Y X s).image x:= womb (gold Y X x p q hk hY) s
omit hk hY
include hj
lemma ocean (s:Cart ι β):badgeK X ((E).finsetCongr s)=(badgeK X s).image x:=by unfold badgeK; rw [(outfits p q _).1]; exact womb hj _
include hk hY
lemma jewels (s:Cart ι β): gemD Y X s ↔ gemD Y X ((E).finsetCongr s):=by
   unfold gemD; refine and_congr ?_ (and_congr ?_ (PhysicalNext.Repeat.Turn.seam (E) x (fun i=> (display x _ _).1 (gold Y X x p q hk hY i)) ((given _ _ _).1 rfl))) -- given loc
   · unfold suit; rw [(outfits p q _).1,(outfits p q _).2]; apply and_congr (sepR hk _)
     conv_rhs=> rw [← p.forall_congr_right]
     refine forall_congr' fun i=>imp_congr ((given p _ _).1 rfl _) (not_congr ?_); rw [hY, ocean X x p q hj, Finset.disjoint_image x.injective]
   rw [(outfits p q _).1]; simp
lemma phones (hp: Continuous K)(hf:(flags t U).image x=flags t V)
 (ha :∀ i, K (Y.mean i U)=Y.mean (p i) V) (hb:∀ i,K (X.warp i U)=X.warp (q i) V)(s :Cart ι β): K (payer Y X t U s)=payer Y X t V ((E).finsetCongr s):=by
    unfold payer; let v:= (E).finsetCongr s; have hh : flags t U ∩ scopeK Y X s=badgeK X s↔ flags t V∩ scopeK Y X v= badgeK X v:=by
       unfold v; rw [wingP Y X x p q hk hY, ocean X x p q hj,← hf,← Finset.image_inter _ _ x.injective, (Finset.image_injective x.injective).eq_iff]
    unfold v at hh; split; swap; · rename_i hn; rw [map_zero,if_neg (mt hh.mpr hn)]
    rename_i he; rw [if_pos (hh.mp he)]
    rw [map_prod]; erw [prod_map]; refine prod_congr rfl fun i _=>?_ ; rcases i with i|i; · exact hb i
    change K (sparkY Y U i)=sparkY Y V (p i); rw [sparkY,map_sub,map_one,map_exp _ hp,ha]; rfl
omit hk hY hj in
lemma wheel (pY:Y.Garish) (hp:MixedP X) (t:ℝ): MixedP (Trail Y X t):=by
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
end YM.QCD.Ruby
