import YM.Intag.Dwells
import YM.Intag.Folio
import YM.Bloom.Calm
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical
namespace Tess
open Pilgrim
variable {l c f:Side}(T:Tiling f)(p:T.Cell)
-- palette ordering and letters use finite prototype *h before L. True orientations.P lift.
variable {I:Type}[Fintype I](x:I→ Cover)(L:List I)
local notation "Jv"=> T.Cell × I
noncomputable abbrev shove (r:T.Cell): T.Cell ≃ T.Cell:= Equiv.swap (μ T p r) r
noncomputable abbrev shows (r:T.Cell): (T.Cell × I) ↪ (T.Cell × I):= Embedding.prodMap ((shove T p r).toEmbedding) (Embedding.refl _)
noncomputable def letter (r:T.Cell):List (T.Cell×I):= if hi:r=p then L.map (Prod.mk p) else (letter (μ T p r)).reverse.map (shows T p r)
termination_by dT T p r
decreasing_by exact (forester T p hi).1
variable (hT:T.kind=.link)(hx:L.Nodup)(hL:∀ i,i∈L)
lemma at_p: letter T p L p=L.map (Prod.mk p):=by rw [letter, dif_pos rfl] -- conflict
local notation "W" i:arg=>letter T p L i
local notation "θ" i:arg => shows (I:=I) T p i
include hx hL
lemma wealthT (r:T.Cell): (letter T p L r).Nodup ∧ (∀ x:T.Cell × I,x∈ letter T p L r ↔ x.1=r):=by
     rw [letter]; split_ifs with h; subst r; exact ⟨hx.map (Prod.mk_right_injective p),fun x=> ⟨fun hh=> by obtain ⟨i,_,hp⟩:= List.mem_map.mp hh; subst x; rfl,fun hh=> List.mem_map.mpr ⟨x.2,hL x.2,Prod.ext hh.symm rfl⟩⟩⟩
     let u:=μ T p r; have ht:= wealthT u; refine ⟨(show (letter T p L u).reverse.Nodup from (by simpa only [List.nodup_reverse] using ht.1)).map (θ r).injective,?_⟩
     rintro ⟨a,x⟩; rw[List.mem_map]; constructor; · rintro ⟨⟨w,y⟩,hy,hp⟩; have hW:= ((ht.2 (w,y)).mp (List.mem_reverse.mp hy)); change w=u at hW; change a=r; exact ((congr_arg Prod.fst hp).symm.trans (by change Equiv.swap u r w = r; rw [hW,Equiv.swap_apply_left]))
     intro hx; change a=r at hx; subst a; exact ⟨(u,x),List.mem_reverse.mpr ((ht.2 _).mpr rfl), Prod.ext (Equiv.swap_apply_left ..) rfl⟩
termination_by dT T p r
decreasing_by exact (forester T p h).1
lemma muster : Folio.Muster (p:=T.period) Prod.fst (letter T p L):= ⟨fun i=> (wealthT T p L hx hL i).1,fun i x=> (wealthT T p L hx hL i).2 x⟩
omit hx hL
open UV UV.Free
-- positions: relative distances at resolution.He.VOasis stamps. Geometry strict margins relative letter array orbits. 
include hT
noncomputable abbrev hof (h:T.kind=.link)(x:I→ Cover)(j : T.Cell× I):= Pilgrim.bout T p h (x j.2) j.1
-- cast warning hT included double.Syntax.
local notation "Φ"=> hof T p hT x
lemma spec (x:Cover)(hp:T.kind=.link): bout T p hp x p=x:=by rw[bout, dif_pos rfl]
-- sparse, no seam wrap.U.PROVE. geometric copy.

lemma cups_f (v:T.Cell)(k j:I): separation ((wrap f ∘ hof T p hT x) (v,k)) ((wrap f ∘ hof T p hT x) (v,j))=separation (wrap f (x k)) (wrap f (x j)):=by
     obtain ⟨w,hw⟩:= T.pointed p (wrap f (x k)); obtain ⟨z,hz⟩:= T.pointed p (wrap f (x j)); change separation (wrap f (bout T p hT (x k) v)) (wrap f (bout T p hT (x j) v))=_; rw [quail T p hT _ _ hw, quail T p hT _ _ hz,←hw,←hz]; simp only [Tiling.copyMap,affine,separation_translate,separation_signed]
lemma prices_f (v:T.Cell)(k:I)(r:ℕ)(hv: wrap f (x k) ∈ T.margin p r): (wrap f∘Φ) (v,k)∈ T.margin v r:=by
     obtain ⟨u,hu⟩:= T.pointed p (wrap f (x k)); change wrap f (bout T p hT _ _) ∈ T.margin v r; rw [quail T p _ _ _ hu]; rw [←hu] at hv; exact (T.reflected_margin ..).mp ((T.reflected_margin ..).mpr hv)
-- Oasis at any offsets.Pregnancy.Use.
omit hT
open QCD.Bera YM.Bloom.Jar YM.Bank.Jule MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden
variable (w:ℝ)(n:ℕ)
lemma arc_s (s:Signed) (x:Cover): posT w n (s.act x)=Ortho.move (Signed.ortho s) (posT w n x):=by
     change _ = Ortho.motion (Signed.ortho s) (_ • _); rw[map_smul, Ortho.motion_at,Signed.ortho_move]; unfold posT; apply congr_arg; ext1 i; obtain ⟨j,rfl⟩:= s.perm.surjective i; change (↑(s.act x (s.perm j)):ℝ)=(s.act _ _) ; rw [Signed.act_at, Signed.act_at]; split <;> simp [YM.Bank.Kith.rock] -- namespace Kith
include hT hx hL
local notation "Xt"=> (posT w n) ∘ Φ
open MassiveQCD.Inky
lemma neighbors (r:T.Cell)(h:r≠p)(u:T.Cell × I)(hh:u∈ letter T p L (μ T p r)):((posT w n) ∘ hof T p hT x) ((θ r) u)= UV.Free.Lyre.crossV (post T p r).2 (posT w n (passport T p hT (u:=r))) ((posT w n) ∘ hof T p hT x) u :=by
      have hp := (wealthT T p L hx hL (μ T p r)).2 u |>.mp ‹_›
      change posT w n (Pilgrim.bout T p hT (x u.2) _) = _ -- reducible shows second
      rw [show ((θ r) u).1=r from (?_),Pilgrim.bout,dif_neg h,spread,arc_s,add_comm]; change _= _ + Ortho.move _ (posT w n (Pilgrim.bout T p hT _ _)); rw [hp]; rfl -- test
      change Equiv.swap (μ T p r) r u.1=r; rw[hp,Equiv.swap_apply_left]
omit hx hL
variable {a b:ℝ}
lemma wonder (r:T.Cell)(i j:I) : ‖(posT w n ∘ hof T p hT x) (r,i) - (posT w n ∘ hof T p hT x) (r,j)‖ = ‖posT w n (x i)-posT w n (x j)‖:=by
      let u:=μ T p r; let Ya (y:I)(v:T.Cell):= posT w n (bout T p hT (x y) v); change ‖Ya i r-Ya j r‖=_; by_cases h:r=p; · subst r; simp only [Ya,spec T p hT]
      have hp := wonder u i j; change ‖Ya i u-Ya j u‖= _ at hp
      let H : Signed:= Signed.mirror (post T p r).2; have hx(y:I): Ya y r=Ortho.motion (Signed.ortho H) (Ya y u)+posT w n (passport T p hT (u:=r)):=by
           unfold Ya; conv_lhs=> rw [bout,dif_neg h,spread,arc_s]
           rfl
      rw[hx,hx,add_sub_add_right_eq_sub,← map_sub,LinearIsometryEquiv.norm_map,hp] -- lemma name
termination_by dT T p r
decreasing_by exact (forester T p h).1
lemma palm (h:0<a)(hw:∀ i j:I,i≠j→ posT w n (x i)-posT w n (x j) ∈ Oasis a b):∀ t∈Folio.ink (show T.Cell × I→ Site T.period from Prod.fst),PalmT (Xt) t a b:=by
     intro t ht; refine ⟨h,?_⟩; rintro ⟨y,i⟩ hv ⟨z,j⟩ hx hf
     have ht0:y=z:=(Folio.ort ..).mp ht _ hv _ hx; subst y; have hp:=hw i j (fun h=>hf (Prod.ext rfl h)); obtain ⟨hs,hL⟩:= consp hp; apply YM.Bloom.Jar.disc <;> rw [wonder T p x hT w n z i j]; exacts [hs,hL]
end Tess
end YM.Intag
#print axioms YM.Intag.Tess.prices_f
#print axioms YM.Intag.Tess.wealthT
#print axioms YM.Intag.Tess.neighbors
#print axioms YM.Intag.Tess.palm
