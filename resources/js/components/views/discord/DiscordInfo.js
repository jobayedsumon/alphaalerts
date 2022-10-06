import {CButton, CCard, CCardBody, CCardHeader, CCol, CFormInput, CFormLabel, CRow} from "@coreui/react";
import React, {useEffect, useState} from "react";
import fetchWrapper from "../../helpers/fetchWrapper";
import {useDispatch, useSelector} from "react-redux";

const DiscordInfo = () => {
    const token = useSelector(state => state.token);
    const dispatch = useDispatch();
    const [discordUser, setDiscordUser] = useState({
        id: '',
        name: '',
        nickname: '',
    });

    const disconnectDiscord = () => {
        fetchWrapper.get('/api/discord-disconnect')
            .then(response => {
                const data = response.data;
                if (data.status === 'success') {
                    setDiscordUser({
                        id: '',
                        name: '',
                        nickname: '',
                    });
                    window.location.reload()
                }
            }).catch(error => {
        });
    }

    useEffect(() => {
            fetchWrapper.get('/api/discord-info')
                .then(response => {
                        const data = response.data;
                        if (data.status === 'success') {
                            setDiscordUser(data.discordUser);
                        }
                    }
                ).catch(error => {
            });
        }
        , []);

    return  <CCard className="mb-5">
        <CCardHeader className="fs-5 d-flex justify-content-between">
            <span>Discord Info</span>
            {discordUser && discordUser.id ?
                <CButton className="btn-danger" onClick={disconnectDiscord}>Disconnect Discord</CButton>
                : <a className="btn btn-primary" href={`/api/discord-connect?token=${token}`}>Connect Discord</a>}

        </CCardHeader>
        <CCardBody>
            <CRow className="mb-3">
                <CCol md="12">
                    <CFormLabel>Discord Name</CFormLabel>
                    <CFormInput disabled={true} type="text" defaultValue={discordUser?.name} />
                </CCol>
            </CRow>
            <CRow className="mb-3">
                <CCol md="12">
                    <CFormLabel>Discord ID</CFormLabel>
                    <CFormInput disabled={true} type="text" defaultValue={discordUser?.discord_id} />
                </CCol>
            </CRow>
            <CRow className="mb-3">
                <CCol md="12">
                    <CFormLabel>Discord Nickname</CFormLabel>
                    <CFormInput disabled={true} type="text" defaultValue={discordUser?.nickname} />
                </CCol>
            </CRow>
        </CCardBody>
    </CCard>
}

export default DiscordInfo;
