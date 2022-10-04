import React, {useEffect, useState} from "react";
import {
    CButton,
    CCard,
    CCardBody,
    CCardHeader,
    CCol,
    CForm,
    CFormInput,
    CFormLabel,
    CInputGroup,
    CRow
} from "@coreui/react";
import {Link} from "react-router-dom";
import CustomTable from "../../common-components/CustomTable";
import {connectDiscord, disconnectDiscord, discordInfo} from "../../helpers/discordHelper";
import fetchWrapper from "../../helpers/fetchWrapper";

const Discord = () => {

    const [discordUser, setDiscordUser] = useState({
        id: '',
        name: '',
        nickname: '',
        servers: []
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

    const columns = [
        {
            name: 'SERVER ID',
            selector: row => row.id,
            sortable: true,
        },
        {
            name: 'SERVER NAME',
            selector: row => row.name,
            sortable: true,
        },
        {
            name: 'ACTION',
            selector: row => <div>
                <Link to={`/discord-server/${row.id}`} className="btn btn-primary btn-sm">
                    <i className="fa fa-eye"></i>
                </Link>
            </div>,
        },
    ];

    const data = discordUser?.servers || [];

    return <>
        <CCard className="mb-5">
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

        <CustomTable title="Discord Server Announcements" columns={columns} data={data} />
    </>
}

export default Discord;
