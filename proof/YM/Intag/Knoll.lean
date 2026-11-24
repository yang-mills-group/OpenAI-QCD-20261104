import YM.Intag.Hickory
import YM.Intag.Beliefs
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Hickory
open Pilgrim Tess Hymnal
open MassiveQCD.Inky YM.Bloom QCD.Bera Massive.UV YM.Arise YM.Arise.Bill YM.Arise.Count YM.Arise.Range Arise.Parcel
open YM.Eden QCD.Lat Massive.Evo MassiveQCD MassiveQCD.TimesV
open UV UV.Free QCD.Grass
open QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Sample Quills Quills.Eden Cupola Ribbon
open Massive.Elm.SparK.Arbor Massive.Elm.SparK.Arbor.Gallery
open QCD.Plum QCD.RP QCD.Cove QCD.Creek QCD.Bloom Metric Laurent Precision Bloch Exterior
open Column
variable {S:Scheme}{R:Side}{i j k p N:ℕ}(A: Massive.Run S N R 6)
variable (hv:p ≤ i)(he:i≤ N)(x:Site (S.side R i))(ho:Even R.val)
local notation "hp"=> Massive.Patria.Hub.evenW S R ho p
local notation "T★"=> mural (viewW S R hv) hp x
local notation "T₀"=> Column.sky S R p N (hv.trans he) hp x
--
variable (K: Site (S.side R p))
-- seam ready at T★ even if i held. no need `T₀=actual Suburb`. include lifts for every v. sigma precise. Scope caution Caret.
lemma foilC (u: Stud (S.side R i) 6)(hU:Tide.Stays u)(a:Axis) : tallH ((Column.sky S R p N (hv.trans he) hp x).bandCut K a) (climbH A i N u)= climbH A i N (tallH ((mural (viewW S R hv) hp x).bandCut K a) u):=by
    let C (k:ℕ):Cells.Cut (S.side R k):= if h:p≤ k then (sky S R p k h hp x).bandCut K a else (mural (viewW S R (le_refl k)) (Massive.Patria.Hub.evenW S R ho k) 0).bandCut (0: Site (S.side R k)) a
    have HT : C i=(mural (viewW S R hv) hp x).bandCut K a:=by unfold C Column.sky; rw [dif_pos hv,homes S R]
    have hf : (C i).kind =.link := HT ▸ rfl -- direction
    have h:=full_tall A C u hU hf (fun k h ht=>?_) he
    · rw [HT,show C N=_ from (dif_pos (hv.trans he): C N=(Column.sky S R p N (hv.trans he) hp x).bandCut K a)] at h; exact h
    have hu:= hv.trans h; unfold C; rw [dif_pos (Nat.le_succ_of_le hu),dif_pos hu]; exact Column.halos S R x hp K hv h a -- arity
variable {I:Type}[Fintype I](z:I→ Cover)(L:List I)(sy:RawSym){D:ℕ}(P:I→ Glyph D)
variable {K0:Clip}(H:Bed)(Q:YM.Next.Free.Train j) {α β w η:ℝ}{c:Side}
local notation "Jq"=> Site (S.side R p) × I
local notation "PP"=> siteP (T★) K sy P
set_option quotPrecheck false
local notation "IK"=> fun v:Jq=> (P v.2).width
local notation "qv"=> fun v:Jq=> polarity (P v.2).spin
local notation "P0"=> hof (T★) K (show (T★).kind=.link from rfl) z
variable (h:∀ i':(Site (S.side R p) × I),(milky 0 H c (G:=su) (d':=(P i'.2).width)).IsSymm)
-- suppose startup Stud at scheme views physical true.Stays and Fence. Yp op equality, Xi from §Body.Actor.Service under ANY seam. then every reflection word valid representative.
local notation "Op"=> opening (sy:=sy) (T★) K z P H Q (show (mural (viewW S R hv) hp x).kind=.link from rfl) w η h
variable (X:Site (S.side R p) × I→Stud (S.side R i) 6)
variable (hP:∀ j:Site (S.side R p)×I,X j=⇑(opening (sy:=sy) ((Massive.Romance.mural (viewW S R hv) (Massive.Patria.Hub.evenW S R ho p) x)) K z P H Q rfl w η h j))
variable (hx:∀ i': (Site (S.side R p) × I), Stays (X i')) (hH: ∀ i': (Site (S.side R p) × I),∀ U, Grass.Hom (polarity (P i'.2).spin) ((X i') U))
variable (ht:Floor H K0 c α β)(ha:0<α)(h₁:Bid.Sworn H c su)(hQ:2≤j)
variable (S₁: Finset (Site (S.side R p)× I)→ Patio (Spine (Site (S.side R p) × I)))
local notation "Rv" i:arg=> letter (T★) K L i
local notation "W0"=> tokenV A qv X hH hx he
local notation "Φ" v:arg=> post T★ K v
local notation "Z!" v:arg=> shows (I:=I) (T★) K v
local notation "μ" v:arg=> Pilgrim.μ (T★) K v -- clash prior Hickory file local gone.
local notation "Palm" => fun i:Site (S.side R p)=> tokenV A qv X hH hx he (Rv i) S₁
local notation "Scan"=> stampU (Keys (S.side R N) 6) IK (YM.Bloom.Jar.posT w (S.J k)∘ P0) -- don't use pos power.W*^(z) must choose.He
local notation "C!" v:arg=> (Column.sky S R p N (hv.trans he) hp x).bandCut (Φ v).1 (Φ v).2
local notation "Q'"=> fun i':Jq=> Arise.Bill.port qv IK i' ((PP) i').source
-- parametric Finset api compensating noncanonical DecidableEq
lemma bind_dest {I:Type}[DecidableEq I](l:List I)(p:Finset I)(h:p∈ bindV l): p.Nonempty ∧ p⊆ l.toFinset:=by
     constructor; · letI:DecidableEq I:=Classical.decEq I; exact Finset.nonempty_iff_ne_empty.mpr (ne_of_mem_erase h) -- should classical vs instance inside. 
     intro i hi; apply List.mem_toFinset.mpr

     letI:DecidableEq I:=fun x y=> Classical.propDecidable _; exact List.mem_toFinset.mp ((mem_powerset.mp (mem_of_mem_erase h)) hi)
lemma bind_mapV {I:Type}(v:List I)(p:Finset I)(f':I↪I) (hp0:p∈Quills.Eden.bindV v):Finset.map f' p∈ Quills.Eden.bindV (v.reverse.map f'):=by
     apply mem_erase.mpr; refine ⟨Finset.nonempty_iff_ne_empty.mp (?_),mem_powerset.mpr ?_⟩
     · exact Finset.map_nonempty.mpr (Finset.nonempty_iff_ne_empty.mpr (ne_of_mem_erase hp0))
     intro i hi; obtain ⟨j,hj,rfl⟩:= mem_map.mp hi; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,List.mem_reverse.mpr (List.mem_toFinset.mp ((mem_powerset.mp (mem_of_mem_erase hp0)) hj)),rfl⟩)
variable (Y:ℝ)(nℓ:ℕ)
local notation "B!"=> YM.Bloom.Jar.posT Y nℓ ∘ hof (T★) K (show (mural (viewW S R hv) hp x).kind=.link from rfl) z
variable (hN:L.Nodup) (hu:∀ i:I,i∈ L)
variable (hΩ:∀ r:Site (S.side R p), Set.InjOn (YM.Bloom.Jar.posT Y nℓ ∘ hof ((Massive.Romance.mural (viewW S R hv) (Massive.Patria.Hub.evenW S R ho p) x)) K (show (mural (viewW S R hv) (Massive.Patria.Hub.evenW S R ho p) x).kind=.link from rfl) z) ((letter (Massive.Romance.mural (viewW S R hv) (Massive.Patria.Hub.evenW S R ho p) x) K L r).toFinset:Set ((Massive.Romance.mural (viewW S R hv) (Massive.Patria.Hub.evenW S R ho p) x).Cell × I)))
local notation "Π!"=> univ (α:=Site (S.side R p))
local notation "Yc"=> (inkV -- placeholder
                      )
local notation "Φc"=>Folio.ink (show Jq→Site (S.side R p) from Prod.fst)
variable (hΘ: ∀ t∈ (Folio.ink (show (Site (S.side R p) × I)→Site (S.side R p) from Prod.fst)).erase ∅, Honest (I:=(Site (S.side R p) × I)) (fun v:Site (S.side R p)× I=> polarity (P v.2).spin) t (S₁ t))
variable (Mode: Bool)
variable (heA: if Mode then (∀ v∈(Folio.ink (show (Site (S.side R p) × I)→Site (S.side R p) from Prod.fst)).erase ∅, qraft (Keys (S.side R N) 6) (Spine (Site (S.side R p) × I)) (S₁ v) = - Play.Chamber.cetacea (Arise.Count.pence (stampU (Keys (S.side R N) 6) (fun v:Site (S.side R p)× I=> (P v.2).width) (YM.Bloom.Jar.posT Y nℓ ∘ hof (Massive.Romance.mural (viewW S R hv) (Massive.Patria.Hub.evenW S R ho p) x) K (show (Massive.Romance.mural (viewW S R hv) (Massive.Patria.Hub.evenW S R ho p) x).kind=.link from rfl) z)) (fun i':(Site (S.side R p) × I)=> Arise.Bill.port (fun v:Site (S.side R p)× I=> polarity (P v.2).spin) (fun v:Site (S.side R p)× I=> (P v.2).width) i' ((siteP (Massive.Romance.mural (viewW S R hv) (Massive.Patria.Hub.evenW S R ho p) x) K sy P i').source))) v) else S₁=0)
include ht ha h₁ hQ hP hx hH hΘ heA hΩ hN hu
set_option maxHeartbeats 1000000
lemma jewel (r:Site (S.side R p))(hr:r≠K): let u:=Pilgrim.μ (T★) K r; let v:= letter (T★) K L; let F:= tokenV A (fun i':Site (S.side R p)× I=> polarity (P i'.2).spin) X hH hx he; F (v r) S₁=tallH ((Column.sky S R p N (hv.trans he) hp x).bandCut (post (T★) K r).1 (post (T★) K r).2) (F (v u) S₁):=by -- syntax.(hp:hO before L!).
    intro u v F; let W : (Site (S.side R p) × I) ↪ (Site (S.side R p) × I) :=shows (I:=I) (T★) K r; let a:= Pilgrim.post (T★) K r; let g:Tiling _:= T₀
    let C:Cells.Cut _:= (Column.sky S R p N (hv.trans he) hp x).bandCut a.1 a.2
    let Y'(j:Jq):= climbH A i N (X j); have hh(j)(U): Hom ((qv) j) (Y' j U):= steep A _ _ (hx j) (hH j) he U
    have hvk : v r=(v u).reverse.map W :=by
        show Tess.letter (T★) K L r=_; rw [Tess.letter]; split_ifs
        next hg=> exact False.elim (hr hg)
        rfl
    rw [hvk]; change exciteE qv Y' hh _ _= tallH _ (exciteE _ _ hh _ _)
    have hM:Folio.Muster (p:=S.side R p) Prod.fst (show Site (S.side R p)→List (Site (S.side R p)× I) from Tess.letter (T★) K L):=Tess.muster (T★) K L hN hu; have hz(v':Site (S.side R p))(t:Finset Jq)(ht:t∈bindV (v v')): t∈(Folio.ink (show Jq→ Site (S.side R p) from Prod.fst)).erase ∅:=by
         have hv':= bind_dest (I:=Jq) (v v') t ht; apply mem_erase.mpr; refine ⟨hv'.1.ne_empty,(Folio.ort ..).mpr fun i hi j hj=> (?_)⟩; exact Eq.trans ((hM.address _ i).mp (List.mem_toFinset.mp (hv'.2 hi))) ((hM.address _ j).mp (List.mem_toFinset.mp (hv'.2 hj))).symm
    refine Massive.Lyre.reflected (I:=Jq) (J:=Jq) (qv) (qv) W (fun _=>rfl) Y' Y' hh hh _ S₁ C (hM.order _) S₁ ?_ ?_ (fun i hi=>hΘ _ (hz u i hi)) -- arity
    · intro j hj
      have hh:tallH ((mural (viewW S R hv) hp x).bandCut a.1 a.2) (X j)= X (W j):=by rw [hP, hP]; exact earns T★ K z P H Q rfl w η h ht ha h₁ hQ r hr j ((hM.address ..).1 hj)
      exact (congr_arg (climbH A i N) hh.symm).trans (foilC A hv he x ho a.1 (X j) (hx j) a.2).symm
    intro M V hV j hj; cases Mode with
    | false=> rw[if_neg (by decide)] at heA; simp only [heA,Pi.zero_apply,map_zero] -- ring
    | true=>
          rw [if_pos rfl] at heA; have hY:j.map W∈bindV (v r):=by rw[hvk]; exact bind_mapV (v u) j (shows T★ K r) hj
          rw [heA j (hz u j hj), heA (j.map W) (hz r _ hY),map_neg]; apply congr_arg; exact Hymnal.obey (T★) K z L sy P hN hu rfl Y nℓ r hr M V hV (hΩ u) _ ((bind_dest ((Rv u)) _ hj).2) -- h
end Hickory
end YM.Intag
#print axioms YM.Intag.Hickory.foilC
#print axioms YM.Intag.Hickory.jewel
