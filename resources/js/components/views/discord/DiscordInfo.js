import {CButton, CCard, CCardBody, CCardHeader, CCol, CFormInput, CFormLabel, CRow} from "@coreui/react";
import {connectDiscord, disconnectDiscord} from "../../helpers/discordHelper";
import React, {useEffect, useState} from "react";
import fetchWrapper from "../../helpers/fetchWrapper";

const DiscordInfo = () => {
    const [discordUser, setDiscordUser] = useState({
        id: '',
        name: '',
        nickname: '',
    });

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
            {discordUser && discordUser.id ? <CButton className="btn-danger" onClick={disconnectDiscord}>Disconnect Discord</CButton> : <CButton onClick={connectDiscord}>Connect Discord</CButton>}

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
